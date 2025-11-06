//! Lifetime-tied linear tokens and counting traits.
//!
//! Tokens are zero-sized proofs that a unit was acquired from a
//! particular counter type. Dropping a token panics; the only valid
//! way to dispose of it is to return it to the originating counter via
//! `Count::put`.
//!
//! Goals
//! - Provide a lifetime-driven API that forces balanced reference counting without relying on caller discipline.
//! - Use zero-sized, linear tokens whose destruction panics unless they are returned to their originating counter.
//! - Make ownership/liveness of map internals easy to reason about: entries keep their backing owner alive; user-facing refs are guaranteed tracked and released.
//!
//! Abstraction
//! - Count: an object that mints and reclaims a unit “reference” by returning a `Token` and later accepting it back. `Count` is the sole place where increments and decrements occur.
//! - Token: a zero-sized, non-cloneable proof that one unit was acquired. It is lifetime-bound and its `Drop` panics to catch unbalanced flows. The only valid disposal is passing it to `Count::put`.
//!
//! Why the type system helps
//! - Origin binding (type-level only): `Token<'a, C>` uses two markers to separate lifetime from the counter type: `PhantomData<&'a ()>` tracks the lifetime, and `PhantomData<*const C>` brands the token to the counter type without requiring `C: 'a`.
//! - Branding is to the counter type, not to a specific counter instance; it does not prevent returning a token to a different instance of the same counter type. Higher-level APIs are responsible for pairing tokens with their originating instance.
//! - Linearity and balance: `Token` does not implement `Copy` or `Clone`, so it cannot be duplicated. Each `get` yields exactly one `Token` that must be consumed by exactly one `put`. Dropping a `Token` instead of returning it panics, catching unbalanced flows.
//! - Zero cost: Tokens are ZSTs; they add no runtime footprint and no allocation. The only costs are the underlying counter operations.
//!
//! Unwinding and Drop panics
//! - Panicking in `Token::drop` during another unwind aborts. Tokens are an internal mechanism, so this fail-fast behavior is acceptable for this crate.
//!
//! Patterns
//! - Owned-token pattern: When a function owns the token and can consume it by value (i.e., not in a `Drop` impl), prefer moving the token directly into `Count::put` without `ManuallyDrop`.
//!   For example, `CountedHandle` owns `Token<'_, UsizeCount>`. `CountedHashMap::put(self, handle)` consumes `handle`, moves out its token by value, and calls `entry.refcount.put(token)`.
//! - Branch-free Drop with `ManuallyDrop`: If the token must be held inside a type that implements `Drop` and the token isn’t owned by value at drop time, store it in `core::mem::ManuallyDrop<Token<...>>` and move it out in `Drop` via `ManuallyDrop::take` to avoid implicit drops and extra branches.
//!
//! Owned + destructuring example
//! ```rust,ignore
//! use crate::tokens::{Count, Token, UsizeCount};
//!
//! // A handle-like wrapper that owns a linear token.
//! struct MyHandle<'a> {
//!     token: Token<'a, UsizeCount>,
//!     counter: &'a UsizeCount,
//! }
//!
//! // By taking `MyHandle` by value, we own its fields. Destructure to move
//! // the token out by value and return it directly — no Drop, no ManuallyDrop.
//! fn release(MyHandle { token, counter }: MyHandle<'_>) -> bool {
//!     counter.put(token)
//! }
//! ```
//!
//! Generic holder pattern
//! ```rust,ignore
//! use core::mem::ManuallyDrop;
//! use crate::tokens::Count;
//!
//! struct Holder<'a, C: Count> {
//!     counter: &'a C,
//!     token: ManuallyDrop<C::Token<'a>>,
//! }
//!
//! impl<'a, C: Count> Holder<'a, C> {
//!     fn new(counter: &'a C) -> Self {
//!         Self { counter, token: ManuallyDrop::new(counter.get()) }
//!     }
//! }
//!
//! impl<'a, C: Count> Drop for Holder<'a, C> {
//!     fn drop(&mut self) {
//!         // SAFETY: We never let `token` be dropped implicitly; move it out exactly once.
//!         let t = unsafe { ManuallyDrop::take(&mut self.token) };
//!         let _ = self.counter.put(t);
//!     }
//! }
//! ```
//!
//! Using the pieces together
//! - Keep the owner alive while any entry exists: `RcHashMap` stores a keepalive `Token<'static, RcCount<Inner>>` per entry. The token is minted from the map’s `RcCount` on insert and returned when the last user-facing `Ref` to that entry is dropped, ensuring the backing allocation outlives the entry.
//! - Ensure every user Ref is counted and released: `Ref` owns a `CountedHandle` which carries a `Token<'_, UsizeCount>` for the entry’s local refcount. Cloning a `Ref` mints a new token; dropping a `Ref` returns its token. When the per-entry count reaches zero, the entry is unlinked and dropped, then the keepalive token is returned to decrement the owner strong count.
//!
//! Implementation variants
//! - UsizeCount: single-threaded counter using `Cell<usize>` to track outstanding user-facing references to an entry. Increment uses `wrapping_add` and aborts on wrap to 0 (matching `Rc`). Decrement asserts nonzero before subtracting. An `is_zero()` helper checks whether the current count is zero.
//! - RcCount<T>: encapsulates raw `Rc` strong-count inc/dec behind the `Count` interface. Unsafety is internal; callers only manipulate `Token`s. Construct via `RcCount::new(&rc)` or `RcCount::from_weak(&weak)`.
//!
//! Notes
//! - Observing zero: `UsizeCount::put` returns a bool indicating whether the count reached zero. `RcCount::put` returns true iff the strong count was 1 before the decrement (typically false when the map itself also holds a strong `Rc`).
//! - Single-threaded only: `UsizeCount` is not `Sync`, and `RcCount` inherits `Rc`’s `!Send + !Sync` semantics.
//! - Overflow behavior (same as Rc): `UsizeCount::get` performs `wrapping_add(1)`, stores it, then aborts the process if the result is 0.
//! - Debug-only behavior: `RcCount::{get,put}` include debug assertions on liveness via `Weak::strong_count()`. These checks are compiled out in release builds.
//!
//! Alternatives considered
//! - Plain `usize` counts without tokens: relies on discipline and is easy to misuse (double `put`, missing `put` on early return). Tokens significantly reduce misuse by construction, but do not enforce per-instance branding.
//! - Storing a runtime back-pointer in the token: not implemented. Without per-instance branding, cross-instance misuse is technically possible; in this crate we rely on API structure to maintain correct pairing.

use core::cell::Cell;
use core::marker::PhantomData;
use std::rc::{Rc, Weak};

/// Zero-sized, linear token tied to its originating counter via lifetime.
pub struct Token<'a, C: ?Sized> {
    // Lifetime is tracked separately from the counter type to avoid
    // imposing `'a` bounds on `C` (useful for generic counters).
    _lt: PhantomData<&'a ()>,
    _ctr: PhantomData<*const C>,
}

impl<'a, C: ?Sized> Token<'a, C> {
    #[inline]
    pub(crate) fn new() -> Self {
        Self {
            _lt: PhantomData,
            _ctr: PhantomData,
        }
    }
}

impl<'a, C: ?Sized> Drop for Token<'a, C> {
    fn drop(&mut self) {
        // Intentional fail-fast on misuse: token must be consumed by Count::put.
        panic!("Token dropped without Count::put");
    }
}

/// A source of counted references, enforced by linear Token flow.
pub trait Count {
    /// The token type minted by this counter.
    type Token<'a>: Sized
    where
        Self: 'a;

    /// Acquire one counted reference and return a linear token for it.
    ///
    /// We mint tokens with a 'static lifetime parameter. The token itself is
    /// still branded to this counter via its type parameter, and can be
    /// covariantly shortened when returning it via `put`.
    fn get(&self) -> Self::Token<'static>;

    /// Return (consume) a previously acquired token.
    /// Returns true if the count is now zero.
    fn put<'a>(&'a self, t: Self::Token<'a>) -> bool;
}

/// Single-threaded reference counter for entries.
#[derive(Debug)]
pub struct UsizeCount {
    count: Cell<usize>,
}

impl UsizeCount {
    pub fn new(initial: usize) -> Self {
        Self {
            count: Cell::new(initial),
        }
    }

    /// Returns true if the current count is zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.count.get() == 0
    }
}

impl Count for UsizeCount {
    type Token<'a>
        = Token<'a, Self>
    where
        Self: 'a;

    #[inline]
    fn get(&self) -> Self::Token<'static> {
        let c = self.count.get();
        let n = c.wrapping_add(1);
        self.count.set(n);
        if n == 0 {
            // Follow Rc semantics: abort on overflow rather than continue unsafely.
            std::process::abort();
        }
        Token::<'static, Self>::new()
    }

    #[inline]
    fn put<'a>(&'a self, t: Self::Token<'a>) -> bool {
        let c = self.count.get();
        assert!(c > 0, "UsizeCount underflow");
        let n = c - 1;
        self.count.set(n);
        core::mem::forget(t);
        n == 0
    }
}

/// Rc-backed manual counter. Uses raw-pointer strong count manipulation.
pub struct RcCount<T> {
    ptr: *const T,
    weak: Weak<T>,
    _nosend: PhantomData<*mut ()>,
}

impl<T> RcCount<T> {
    pub fn new(rc: &Rc<T>) -> Self {
        let weak = Rc::downgrade(rc);
        let raw = Rc::into_raw(rc.clone());
        unsafe { Rc::decrement_strong_count(raw) };
        Self {
            ptr: raw,
            weak,
            _nosend: PhantomData,
        }
    }

    pub fn from_weak(weak: &Weak<T>) -> Self {
        let raw = weak.as_ptr();
        Self {
            ptr: raw,
            weak: weak.clone(),
            _nosend: PhantomData,
        }
    }
}

impl<T: 'static> Count for RcCount<T> {
    type Token<'a>
        = Token<'a, Self>
    where
        Self: 'a;

    #[inline]
    fn get(&self) -> Self::Token<'static> {
        debug_assert!(self.weak.strong_count() > 0);
        unsafe { Rc::increment_strong_count(self.ptr) };
        Token::<'static, Self>::new()
    }

    #[inline]
    fn put<'a>(&'a self, t: Self::Token<'a>) -> bool {
        debug_assert!(self.weak.strong_count() > 0);
        let was_one = self.weak.strong_count() == 1;
        unsafe { Rc::decrement_strong_count(self.ptr) };
        core::mem::forget(t);
        was_one
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    /// Invariant: Dropping a token without returning it via `Count::put`
    /// panics (fail-fast). This ensures linear token flow is enforced.
    fn token_drop_panics() {
        let c = UsizeCount::new(0);
        let t = c.get();
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(t)));
        assert!(res.is_err());
    }

    #[test]
    /// Invariant: `UsizeCount` reflects the exact number of outstanding
    /// tokens, and `put` returns true when the count reaches zero.
    fn usizecount_balance_and_zero() {
        let c = UsizeCount::new(0);
        let t1 = c.get();
        let t2 = c.get();
        assert!(!c.is_zero());
        assert!(!c.put(t1));
        assert!(c.put(t2));
        assert!(c.is_zero());
    }

    #[test]
    /// Invariant: `RcCount` increments the underlying `Rc` strong count on
    /// `get` and decrements it on `put`. For a live `Rc`, `put` never
    /// indicates the count was one (because the map holds another strong ref
    /// in typical usage).
    fn rccount_increments_and_put_flag() {
        let rc = Rc::new(123);
        let weak = Rc::downgrade(&rc);
        let c = RcCount::new(&rc);
        let before = weak.strong_count();
        let t = c.get();
        assert_eq!(weak.strong_count(), before + 1);
        let was_one = c.put(t);
        assert!(!was_one);
        assert_eq!(weak.strong_count(), before);
    }

    // Property: For arbitrary get/put sequences, `UsizeCount`'s zero/non-zero
    // state matches whether there are tokens outstanding, and `put`'s return
    // value signals transition-to-zero exactly when the last token is returned.
    proptest! {
        #[test]
        fn prop_usizecount_get_put_balance(ops in proptest::collection::vec(0u8..=1, 0..200)) {
            let c = UsizeCount::new(0);
            let mut toks: Vec<Token<'static, UsizeCount>> = Vec::new();
            for op in ops.iter().copied() {
                match op {
                    0 => {
                        toks.push(c.get());
                        assert!(!c.is_zero());
                    }
                    _ => {
                        if let Some(t) = toks.pop() {
                            let now_zero = c.put(t);
                            assert_eq!(now_zero, toks.is_empty());
                            assert_eq!(c.is_zero(), toks.is_empty());
                        }
                    }
                }
            }
            assert_eq!(c.is_zero(), toks.is_empty());
            while let Some(t) = toks.pop() {
                let now_zero = c.put(t);
                assert_eq!(now_zero, toks.is_empty());
            }
            assert!(c.is_zero());
        }

        // Property: Two `UsizeCount` instances are independent; operations on
        // one must not affect the other's zero/non-zero state or put results.
        #[test]
        fn prop_two_usizecounts_independent(ops in proptest::collection::vec((0u8..=1, 0u8..=1), 0..200)) {
            let a = UsizeCount::new(0);
            let b = UsizeCount::new(0);
            let mut ta: Vec<Token<'static, UsizeCount>> = Vec::new();
            let mut tb: Vec<Token<'static, UsizeCount>> = Vec::new();
            for (which, op) in ops.into_iter() {
                match (which, op) {
                    (0, 0) => { ta.push(a.get()); }
                    (0, 1) => {
                        if let Some(t) = ta.pop() {
                            let now_zero = a.put(t);
                            assert_eq!(now_zero, ta.is_empty());
                        }
                    }
                    (1, 0) => { tb.push(b.get()); }
                    (1, 1) => {
                        if let Some(t) = tb.pop() {
                            let now_zero = b.put(t);
                            assert_eq!(now_zero, tb.is_empty());
                        }
                    }
                    _ => unreachable!(),
                }
                assert_eq!(a.is_zero(), ta.is_empty());
                assert_eq!(b.is_zero(), tb.is_empty());
            }

            while let Some(t) = ta.pop() { let _ = a.put(t); }
            while let Some(t) = tb.pop() { let _ = b.put(t); }
            assert!(a.is_zero());
            assert!(b.is_zero());
        }

        // Property: `RcCount` round-trip increments and decrements the strong
        // count by the exact number of outstanding tokens. Returning tokens
        // never reports `was_one` here because another owner (the map) holds
        // a strong reference; the weak strong_count tracks changes.
        #[test]
        fn prop_rccount_roundtrip(n in 0usize..100) {
            let rc = Rc::new(());
            let weak = Rc::downgrade(&rc);
            let c = RcCount::new(&rc);
            let before = weak.strong_count();
            let mut toks: Vec<Token<'static, RcCount<_>>> = Vec::new();
            for _ in 0..n { toks.push(c.get()); }
            assert_eq!(weak.strong_count(), before + n);
            while let Some(t) = toks.pop() {
                let was_one = c.put(t);
                assert!(!was_one);
                assert_eq!(weak.strong_count(), before + toks.len());
            }
            assert_eq!(weak.strong_count(), before);
        }
    }
}
