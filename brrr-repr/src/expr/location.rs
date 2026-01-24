//! Source location tracking
//!
//! Following EverParse's with_meta_t pattern for attaching source spans to AST nodes.

use serde::{Deserialize, Serialize};

/// Source position: file, line, column
/// Maps to F*: type pos = { pos_filename: string; pos_line: nat; pos_col: nat }
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct Pos {
    /// File ID (index into file table, not the path itself)
    pub file_id: u32,
    /// Line number (1-indexed)
    pub line: u32,
    /// Column number (1-indexed, in UTF-8 code points)
    pub col: u32,
}

impl Pos {
    /// Create a new position
    pub const fn new(file_id: u32, line: u32, col: u32) -> Self {
        Self { file_id, line, col }
    }

    /// Synthetic/unknown position
    pub const SYNTHETIC: Self = Self {
        file_id: u32::MAX,
        line: 0,
        col: 0,
    };

    /// Is this a synthetic (unknown) position?
    pub const fn is_synthetic(self) -> bool {
        self.file_id == u32::MAX
    }

    /// Format as string (requires file table for full path)
    pub fn format(&self, file_table: &[String]) -> String {
        if self.is_synthetic() {
            "<synthetic>".to_string()
        } else {
            let file = file_table
                .get(self.file_id as usize)
                .map_or("<unknown>", String::as_str);
            format!("{}:{}:{}", file, self.line, self.col)
        }
    }

    /// Format as «file:line:col» for .brrrx
    pub fn format_brrrx(&self) -> String {
        if self.is_synthetic() {
            "«synthetic»".to_string()
        } else {
            format!("«#{}:{}:{}»", self.file_id, self.line, self.col)
        }
    }
}

/// Source range: start to end position
/// Maps to F*: type range = pos * pos
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct Range {
    pub start: Pos,
    pub end: Pos,
}

impl Range {
    /// Create a new range
    pub const fn new(start: Pos, end: Pos) -> Self {
        Self { start, end }
    }

    /// Create a range spanning a single position
    pub const fn point(pos: Pos) -> Self {
        Self {
            start: pos,
            end: pos,
        }
    }

    /// Synthetic/unknown range
    pub const SYNTHETIC: Self = Self {
        start: Pos::SYNTHETIC,
        end: Pos::SYNTHETIC,
    };

    /// Is this a synthetic (unknown) range?
    pub const fn is_synthetic(self) -> bool {
        self.start.is_synthetic()
    }

    /// Combine two ranges (smallest containing both)
    pub fn union(self, other: Self) -> Self {
        if self.is_synthetic() {
            return other;
        }
        if other.is_synthetic() {
            return self;
        }

        let start = if (self.start.line, self.start.col) < (other.start.line, other.start.col) {
            self.start
        } else {
            other.start
        };

        let end = if (self.end.line, self.end.col) > (other.end.line, other.end.col) {
            self.end
        } else {
            other.end
        };

        Self { start, end }
    }

    /// Check if this range contains a position
    pub fn contains(&self, pos: Pos) -> bool {
        if self.is_synthetic() || pos.is_synthetic() {
            return false;
        }
        if self.start.file_id != pos.file_id {
            return false;
        }

        let after_start =
            (pos.line, pos.col) >= (self.start.line, self.start.col);
        let before_end = (pos.line, pos.col) <= (self.end.line, self.end.col);

        after_start && before_end
    }

    /// Format as string
    pub fn format(&self, file_table: &[String]) -> String {
        if self.is_synthetic() {
            "<synthetic>".to_string()
        } else if self.start == self.end {
            self.start.format(file_table)
        } else {
            format!(
                "{}-{}:{}",
                self.start.format(file_table),
                self.end.line,
                self.end.col
            )
        }
    }

    /// Format as «file:start-end» for .brrrx
    pub fn format_brrrx(&self) -> String {
        if self.is_synthetic() {
            "«synthetic»".to_string()
        } else if self.start.file_id == self.end.file_id {
            format!(
                "«#{}:{}:{}-{}:{}»",
                self.start.file_id,
                self.start.line,
                self.start.col,
                self.end.line,
                self.end.col
            )
        } else {
            format!(
                "«#{}:{}:{}-#{}:{}:{}»",
                self.start.file_id,
                self.start.line,
                self.start.col,
                self.end.file_id,
                self.end.line,
                self.end.col
            )
        }
    }
}

/// Wrapper that attaches source location to any value
/// Following EverParse's with_meta_t pattern:
/// ```fstar
/// noeq type with_meta_t 'a = {
///   v: 'a;
///   range: range;
///   comments: comments
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct WithLoc<T> {
    /// The underlying value
    pub value: T,
    /// Source range
    pub range: Range,
}

impl<T> WithLoc<T> {
    /// Create a new located value
    pub const fn new(value: T, range: Range) -> Self {
        Self { value, range }
    }

    /// Create a synthetic (no location) value
    pub fn synthetic(value: T) -> Self {
        Self {
            value,
            range: Range::SYNTHETIC,
        }
    }

    /// Create with just a position (zero-width range)
    pub fn at(value: T, pos: Pos) -> Self {
        Self {
            value,
            range: Range::point(pos),
        }
    }

    /// Map the inner value, preserving location
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> WithLoc<U> {
        WithLoc {
            value: f(self.value),
            range: self.range,
        }
    }

    /// Map the inner value by reference
    pub fn map_ref<U>(&self, f: impl FnOnce(&T) -> U) -> WithLoc<U> {
        WithLoc {
            value: f(&self.value),
            range: self.range,
        }
    }

    /// Get the inner value, discarding location
    pub fn into_inner(self) -> T {
        self.value
    }

    /// Borrow the inner value
    pub const fn as_ref(&self) -> &T {
        &self.value
    }

    /// Mutably borrow the inner value
    pub fn as_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<T: Default> Default for WithLoc<T> {
    fn default() -> Self {
        Self::synthetic(T::default())
    }
}

impl<T> std::ops::Deref for WithLoc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> std::ops::DerefMut for WithLoc<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T> From<T> for WithLoc<T> {
    fn from(value: T) -> Self {
        Self::synthetic(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pos_format() {
        let pos = Pos::new(0, 10, 5);
        let files = vec!["main.brrr".to_string()];
        assert_eq!(pos.format(&files), "main.brrr:10:5");
    }

    #[test]
    fn test_range_union() {
        let r1 = Range::new(Pos::new(0, 1, 1), Pos::new(0, 1, 10));
        let r2 = Range::new(Pos::new(0, 2, 1), Pos::new(0, 2, 10));
        let union = r1.union(r2);
        assert_eq!(union.start, Pos::new(0, 1, 1));
        assert_eq!(union.end, Pos::new(0, 2, 10));
    }

    #[test]
    fn test_range_contains() {
        let range = Range::new(Pos::new(0, 5, 1), Pos::new(0, 10, 20));
        assert!(range.contains(Pos::new(0, 7, 10)));
        assert!(!range.contains(Pos::new(0, 3, 1)));
        assert!(!range.contains(Pos::new(1, 7, 10))); // Different file
    }

    #[test]
    fn test_with_loc_map() {
        let loc = WithLoc::new(42, Range::new(Pos::new(0, 1, 1), Pos::new(0, 1, 2)));
        let doubled = loc.map(|x| x * 2);
        assert_eq!(doubled.value, 84);
        assert_eq!(doubled.range.start.line, 1);
    }
}
