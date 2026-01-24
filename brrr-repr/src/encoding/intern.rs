//! String interning for efficient serialization using lasso
//!
//! Uses lasso crate for efficient, thread-safe string interning with
//! 4-byte Spur keys for memory efficiency.

use lasso::{Rodeo, RodeoReader, RodeoResolver, Spur};

/// String interner for deduplicating strings during encoding.
/// Uses lasso's Rodeo for efficient O(1) interning and lookup.
#[derive(Debug, Default)]
pub struct StringInterner {
    rodeo: Rodeo,
}

impl StringInterner {
    /// Create a new empty interner
    pub fn new() -> Self {
        Self {
            rodeo: Rodeo::default(),
        }
    }

    /// Create an interner with pre-allocated capacity for strings and bytes
    pub fn with_capacity(strings: usize, bytes: usize) -> Self {
        use std::num::NonZeroUsize;
        let strings_cap = NonZeroUsize::new(strings).unwrap_or(NonZeroUsize::MIN);
        let bytes_cap = NonZeroUsize::new(bytes).unwrap_or(NonZeroUsize::MIN);
        Self {
            rodeo: Rodeo::with_capacity(lasso::Capacity::new(strings_cap.get(), bytes_cap)),
        }
    }

    /// Intern a string, returning its Spur key
    pub fn intern(&mut self, s: &str) -> Spur {
        self.rodeo.get_or_intern(s)
    }

    /// Intern a static string (more efficient for literals)
    pub fn intern_static(&mut self, s: &'static str) -> Spur {
        self.rodeo.get_or_intern_static(s)
    }

    /// Get the key for a string if already interned
    pub fn get(&self, s: &str) -> Option<Spur> {
        self.rodeo.get(s)
    }

    /// Resolve a Spur to its string
    pub fn resolve(&self, spur: Spur) -> &str {
        self.rodeo.resolve(&spur)
    }

    /// Try to resolve a Spur to its string
    pub fn try_resolve(&self, spur: Spur) -> Option<&str> {
        self.rodeo.try_resolve(&spur)
    }

    /// Number of interned strings
    pub fn len(&self) -> usize {
        self.rodeo.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.rodeo.is_empty()
    }

    /// Iterate over all (key, string) pairs
    pub fn iter(&self) -> impl Iterator<Item = (Spur, &str)> {
        self.rodeo.iter()
    }

    /// Convert to a read-only resolver (for decoding phase)
    pub fn into_resolver(self) -> RodeoResolver {
        self.rodeo.into_resolver()
    }

    /// Convert to a read-only reader (can still lookup by string)
    pub fn into_reader(self) -> RodeoReader {
        self.rodeo.into_reader()
    }

    /// Get the underlying Rodeo for advanced operations
    pub fn rodeo(&self) -> &Rodeo {
        &self.rodeo
    }

    /// Get mutable access to the underlying Rodeo
    pub fn rodeo_mut(&mut self) -> &mut Rodeo {
        &mut self.rodeo
    }
}

/// Read-only string resolver for decoding.
/// More memory-efficient than keeping the full Rodeo.
#[derive(Debug)]
pub struct StringResolver {
    resolver: RodeoResolver,
}

impl StringResolver {
    /// Create from a list of strings (in order by index)
    pub fn from_strings(strings: impl IntoIterator<Item = String>) -> Self {
        let mut rodeo = Rodeo::default();
        for s in strings {
            rodeo.get_or_intern(s);
        }
        Self {
            resolver: rodeo.into_resolver(),
        }
    }

    /// Resolve a Spur to its string
    pub fn resolve(&self, spur: Spur) -> &str {
        self.resolver.resolve(&spur)
    }

    /// Try to resolve a Spur to its string
    pub fn try_resolve(&self, spur: Spur) -> Option<&str> {
        self.resolver.try_resolve(&spur)
    }

    /// Number of interned strings
    pub fn len(&self) -> usize {
        self.resolver.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.resolver.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intern_basic() {
        let mut interner = StringInterner::new();
        let a = interner.intern("hello");
        let b = interner.intern("world");
        let c = interner.intern("hello");

        // Same string should return same Spur
        assert_eq!(a, c);
        // Different strings have different Spurs
        assert_ne!(a, b);
        // Only 2 unique strings
        assert_eq!(interner.len(), 2);
    }

    #[test]
    fn test_resolve() {
        let mut interner = StringInterner::new();
        let spur = interner.intern("test string");

        assert_eq!(interner.resolve(spur), "test string");
    }

    #[test]
    fn test_get() {
        let mut interner = StringInterner::new();
        let spur = interner.intern("exists");

        assert_eq!(interner.get("exists"), Some(spur));
        assert_eq!(interner.get("not_exists"), None);
    }

    #[test]
    fn test_resolver() {
        let mut interner = StringInterner::new();
        let a = interner.intern("first");
        let b = interner.intern("second");

        let resolver = interner.into_resolver();
        assert_eq!(resolver.resolve(&a), "first");
        assert_eq!(resolver.resolve(&b), "second");
    }

    #[test]
    fn test_iter() {
        let mut interner = StringInterner::new();
        interner.intern("one");
        interner.intern("two");
        interner.intern("three");

        let pairs: Vec<_> = interner.iter().collect();
        assert_eq!(pairs.len(), 3);

        // Check all strings are present
        let strings: Vec<&str> = pairs.iter().map(|(_, s)| *s).collect();
        assert!(strings.contains(&"one"));
        assert!(strings.contains(&"two"));
        assert!(strings.contains(&"three"));
    }
}
