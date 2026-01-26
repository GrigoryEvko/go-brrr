//! Large Rust module for benchmarking AST extraction.
//!
//! Contains typical Rust patterns including traits, generics, lifetimes,
//! async code, error handling, and macro usage.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fmt::{self, Display, Formatter};
use std::hash::Hash;
use std::io::{self, BufRead, BufReader, Read, Write};
use std::marker::PhantomData;
use std::ops::{Add, Deref, DerefMut, Index, IndexMut, Mul, Sub};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock};

/// Error type for this module.
#[derive(Debug, Clone)]
pub enum Error {
    /// An I/O error occurred.
    Io(String),
    /// A parsing error occurred.
    Parse(String),
    /// A validation error occurred.
    Validation(String),
    /// A not found error.
    NotFound(String),
    /// A timeout error.
    Timeout { operation: String, duration_ms: u64 },
    /// A custom error with details.
    Custom { code: i32, message: String },
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Error::Io(msg) => write!(f, "IO error: {}", msg),
            Error::Parse(msg) => write!(f, "Parse error: {}", msg),
            Error::Validation(msg) => write!(f, "Validation error: {}", msg),
            Error::NotFound(msg) => write!(f, "Not found: {}", msg),
            Error::Timeout {
                operation,
                duration_ms,
            } => write!(f, "Timeout after {}ms: {}", duration_ms, operation),
            Error::Custom { code, message } => write!(f, "Error {}: {}", code, message),
        }
    }
}

impl std::error::Error for Error {}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Error::Io(err.to_string())
    }
}

/// Result type alias using our Error type.
pub type Result<T> = std::result::Result<T, Error>;

/// A trait for items that can be identified.
pub trait Identifiable {
    /// The type of the identifier.
    type Id: Clone + Eq + Hash;

    /// Get the identifier.
    fn id(&self) -> &Self::Id;
}

/// A trait for items that have timestamps.
pub trait Timestamped {
    /// Get the creation timestamp.
    fn created_at(&self) -> u64;

    /// Get the last update timestamp.
    fn updated_at(&self) -> u64;
}

/// A trait for items that can be validated.
pub trait Validatable {
    /// Validate the item, returning errors if invalid.
    fn validate(&self) -> std::result::Result<(), Vec<String>>;

    /// Check if the item is valid.
    fn is_valid(&self) -> bool {
        self.validate().is_ok()
    }
}

/// A trait for serializable items.
pub trait Serializable: Sized {
    /// Serialize to bytes.
    fn to_bytes(&self) -> Vec<u8>;

    /// Deserialize from bytes.
    fn from_bytes(bytes: &[u8]) -> Result<Self>;

    /// Serialize to string.
    fn to_string_repr(&self) -> String {
        String::from_utf8_lossy(&self.to_bytes()).into_owned()
    }
}

/// A generic entity with common fields.
#[derive(Debug, Clone)]
pub struct Entity<T> {
    /// Unique identifier.
    pub id: String,
    /// Creation timestamp.
    pub created_at: u64,
    /// Last update timestamp.
    pub updated_at: u64,
    /// The wrapped data.
    pub data: T,
    /// Optional metadata.
    pub metadata: HashMap<String, String>,
}

impl<T> Entity<T> {
    /// Create a new entity.
    pub fn new(id: impl Into<String>, data: T) -> Self {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
        Self {
            id: id.into(),
            created_at: now,
            updated_at: now,
            data,
            metadata: HashMap::new(),
        }
    }

    /// Update the data.
    pub fn update(&mut self, data: T) {
        self.data = data;
        self.updated_at = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
    }

    /// Add metadata.
    pub fn with_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// Get metadata value.
    pub fn get_metadata(&self, key: &str) -> Option<&String> {
        self.metadata.get(key)
    }

    /// Map the inner data.
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Entity<U> {
        Entity {
            id: self.id,
            created_at: self.created_at,
            updated_at: self.updated_at,
            data: f(self.data),
            metadata: self.metadata,
        }
    }
}

impl<T> Identifiable for Entity<T> {
    type Id = String;

    fn id(&self) -> &Self::Id {
        &self.id
    }
}

impl<T> Timestamped for Entity<T> {
    fn created_at(&self) -> u64 {
        self.created_at
    }

    fn updated_at(&self) -> u64 {
        self.updated_at
    }
}

impl<T> Deref for Entity<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<T> DerefMut for Entity<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

/// A 2D point.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

impl Point {
    /// Create a new point.
    pub const fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    /// Origin point.
    pub const ORIGIN: Self = Self::new(0.0, 0.0);

    /// Calculate distance to another point.
    pub fn distance_to(&self, other: &Point) -> f64 {
        let dx = self.x - other.x;
        let dy = self.y - other.y;
        (dx * dx + dy * dy).sqrt()
    }

    /// Calculate the magnitude (distance from origin).
    pub fn magnitude(&self) -> f64 {
        self.distance_to(&Self::ORIGIN)
    }

    /// Normalize to unit vector.
    pub fn normalize(&self) -> Option<Self> {
        let mag = self.magnitude();
        if mag > 0.0 {
            Some(Self::new(self.x / mag, self.y / mag))
        } else {
            None
        }
    }

    /// Dot product with another point.
    pub fn dot(&self, other: &Point) -> f64 {
        self.x * other.x + self.y * other.y
    }

    /// Cross product with another point.
    pub fn cross(&self, other: &Point) -> f64 {
        self.x * other.y - self.y * other.x
    }

    /// Rotate by angle in radians.
    pub fn rotate(&self, angle: f64) -> Self {
        let cos = angle.cos();
        let sin = angle.sin();
        Self::new(self.x * cos - self.y * sin, self.x * sin + self.y * cos)
    }
}

impl Add for Point {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        Self::new(self.x + other.x, self.y + other.y)
    }
}

impl Sub for Point {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        Self::new(self.x - other.x, self.y - other.y)
    }
}

impl Mul<f64> for Point {
    type Output = Self;

    fn mul(self, scalar: f64) -> Self::Output {
        Self::new(self.x * scalar, self.y * scalar)
    }
}

impl Display for Point {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}

/// A rectangle defined by two corners.
#[derive(Debug, Clone, Copy)]
pub struct Rectangle {
    pub top_left: Point,
    pub bottom_right: Point,
}

impl Rectangle {
    /// Create a new rectangle.
    pub fn new(top_left: Point, bottom_right: Point) -> Self {
        Self {
            top_left,
            bottom_right,
        }
    }

    /// Create from center and dimensions.
    pub fn from_center(center: Point, width: f64, height: f64) -> Self {
        let half_w = width / 2.0;
        let half_h = height / 2.0;
        Self {
            top_left: Point::new(center.x - half_w, center.y - half_h),
            bottom_right: Point::new(center.x + half_w, center.y + half_h),
        }
    }

    /// Get the width.
    pub fn width(&self) -> f64 {
        (self.bottom_right.x - self.top_left.x).abs()
    }

    /// Get the height.
    pub fn height(&self) -> f64 {
        (self.bottom_right.y - self.top_left.y).abs()
    }

    /// Get the area.
    pub fn area(&self) -> f64 {
        self.width() * self.height()
    }

    /// Get the perimeter.
    pub fn perimeter(&self) -> f64 {
        2.0 * (self.width() + self.height())
    }

    /// Get the center point.
    pub fn center(&self) -> Point {
        Point::new(
            (self.top_left.x + self.bottom_right.x) / 2.0,
            (self.top_left.y + self.bottom_right.y) / 2.0,
        )
    }

    /// Check if a point is inside.
    pub fn contains(&self, point: &Point) -> bool {
        point.x >= self.top_left.x
            && point.x <= self.bottom_right.x
            && point.y >= self.top_left.y
            && point.y <= self.bottom_right.y
    }

    /// Check if this rectangle intersects another.
    pub fn intersects(&self, other: &Rectangle) -> bool {
        !(self.bottom_right.x < other.top_left.x
            || self.top_left.x > other.bottom_right.x
            || self.bottom_right.y < other.top_left.y
            || self.top_left.y > other.bottom_right.y)
    }

    /// Get the intersection with another rectangle.
    pub fn intersection(&self, other: &Rectangle) -> Option<Rectangle> {
        if !self.intersects(other) {
            return None;
        }

        Some(Rectangle {
            top_left: Point::new(
                self.top_left.x.max(other.top_left.x),
                self.top_left.y.max(other.top_left.y),
            ),
            bottom_right: Point::new(
                self.bottom_right.x.min(other.bottom_right.x),
                self.bottom_right.y.min(other.bottom_right.y),
            ),
        })
    }

    /// Get the bounding box that contains both rectangles.
    pub fn union(&self, other: &Rectangle) -> Rectangle {
        Rectangle {
            top_left: Point::new(
                self.top_left.x.min(other.top_left.x),
                self.top_left.y.min(other.top_left.y),
            ),
            bottom_right: Point::new(
                self.bottom_right.x.max(other.bottom_right.x),
                self.bottom_right.y.max(other.bottom_right.y),
            ),
        }
    }
}

/// A generic cache with LRU eviction.
pub struct LruCache<K, V> {
    capacity: usize,
    map: HashMap<K, V>,
    order: VecDeque<K>,
}

impl<K: Clone + Eq + Hash, V> LruCache<K, V> {
    /// Create a new cache with the given capacity.
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: HashMap::with_capacity(capacity),
            order: VecDeque::with_capacity(capacity),
        }
    }

    /// Get a value from the cache.
    pub fn get(&mut self, key: &K) -> Option<&V> {
        if self.map.contains_key(key) {
            self.touch(key.clone());
            self.map.get(key)
        } else {
            None
        }
    }

    /// Get a mutable reference to a value.
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        if self.map.contains_key(key) {
            self.touch(key.clone());
            self.map.get_mut(key)
        } else {
            None
        }
    }

    /// Insert a value into the cache.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if self.map.contains_key(&key) {
            self.touch(key.clone());
            self.map.insert(key, value)
        } else {
            if self.map.len() >= self.capacity {
                self.evict();
            }
            self.order.push_back(key.clone());
            self.map.insert(key, value)
        }
    }

    /// Remove a value from the cache.
    pub fn remove(&mut self, key: &K) -> Option<V> {
        if let Some(value) = self.map.remove(key) {
            self.order.retain(|k| k != key);
            Some(value)
        } else {
            None
        }
    }

    /// Check if a key exists.
    pub fn contains(&self, key: &K) -> bool {
        self.map.contains_key(key)
    }

    /// Get the number of items.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Clear the cache.
    pub fn clear(&mut self) {
        self.map.clear();
        self.order.clear();
    }

    fn touch(&mut self, key: K) {
        self.order.retain(|k| k != &key);
        self.order.push_back(key);
    }

    fn evict(&mut self) {
        if let Some(key) = self.order.pop_front() {
            self.map.remove(&key);
        }
    }
}

/// A thread-safe counter.
#[derive(Debug)]
pub struct Counter {
    value: AtomicUsize,
}

impl Counter {
    /// Create a new counter.
    pub const fn new() -> Self {
        Self {
            value: AtomicUsize::new(0),
        }
    }

    /// Create with initial value.
    pub const fn with_value(value: usize) -> Self {
        Self {
            value: AtomicUsize::new(value),
        }
    }

    /// Get the current value.
    pub fn get(&self) -> usize {
        self.value.load(Ordering::SeqCst)
    }

    /// Increment and return new value.
    pub fn increment(&self) -> usize {
        self.value.fetch_add(1, Ordering::SeqCst) + 1
    }

    /// Decrement and return new value.
    pub fn decrement(&self) -> usize {
        self.value.fetch_sub(1, Ordering::SeqCst) - 1
    }

    /// Add and return new value.
    pub fn add(&self, n: usize) -> usize {
        self.value.fetch_add(n, Ordering::SeqCst) + n
    }

    /// Reset to zero.
    pub fn reset(&self) {
        self.value.store(0, Ordering::SeqCst);
    }
}

impl Default for Counter {
    fn default() -> Self {
        Self::new()
    }
}

/// A thread-safe flag.
#[derive(Debug)]
pub struct Flag {
    value: AtomicBool,
}

impl Flag {
    /// Create a new flag.
    pub const fn new() -> Self {
        Self {
            value: AtomicBool::new(false),
        }
    }

    /// Create with initial value.
    pub const fn with_value(value: bool) -> Self {
        Self {
            value: AtomicBool::new(value),
        }
    }

    /// Get the current value.
    pub fn get(&self) -> bool {
        self.value.load(Ordering::SeqCst)
    }

    /// Set the value.
    pub fn set(&self, value: bool) {
        self.value.store(value, Ordering::SeqCst);
    }

    /// Toggle and return new value.
    pub fn toggle(&self) -> bool {
        !self.value.fetch_xor(true, Ordering::SeqCst)
    }

    /// Set to true if currently false.
    pub fn try_set(&self) -> bool {
        self.value
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
    }
}

impl Default for Flag {
    fn default() -> Self {
        Self::new()
    }
}

/// A simple state machine.
pub struct StateMachine<S, E> {
    current: S,
    transitions: HashMap<(S, E), S>,
    on_enter: HashMap<S, Box<dyn Fn(&S)>>,
    on_exit: HashMap<S, Box<dyn Fn(&S)>>,
}

impl<S: Clone + Eq + Hash, E: Eq + Hash> StateMachine<S, E> {
    /// Create a new state machine.
    pub fn new(initial: S) -> Self {
        Self {
            current: initial,
            transitions: HashMap::new(),
            on_enter: HashMap::new(),
            on_exit: HashMap::new(),
        }
    }

    /// Add a transition.
    pub fn add_transition(&mut self, from: S, event: E, to: S) {
        self.transitions.insert((from, event), to);
    }

    /// Process an event.
    pub fn process(&mut self, event: E) -> bool {
        let key = (self.current.clone(), event);
        if let Some(next) = self.transitions.get(&key).cloned() {
            if let Some(handler) = self.on_exit.get(&self.current) {
                handler(&self.current);
            }
            self.current = next;
            if let Some(handler) = self.on_enter.get(&self.current) {
                handler(&self.current);
            }
            true
        } else {
            false
        }
    }

    /// Get current state.
    pub fn current(&self) -> &S {
        &self.current
    }
}

/// A builder pattern implementation.
pub struct Builder<T> {
    value: Option<T>,
    validators: Vec<Box<dyn Fn(&T) -> std::result::Result<(), String>>>,
}

impl<T: Default> Builder<T> {
    /// Create a new builder.
    pub fn new() -> Self {
        Self {
            value: Some(T::default()),
            validators: Vec::new(),
        }
    }

    /// Set the value.
    pub fn with_value(mut self, value: T) -> Self {
        self.value = Some(value);
        self
    }

    /// Add a validator.
    pub fn validate<F>(mut self, f: F) -> Self
    where
        F: Fn(&T) -> std::result::Result<(), String> + 'static,
    {
        self.validators.push(Box::new(f));
        self
    }

    /// Build the value.
    pub fn build(self) -> std::result::Result<T, Vec<String>> {
        let value = self.value.ok_or_else(|| vec!["No value set".to_string()])?;
        let errors: Vec<String> = self
            .validators
            .iter()
            .filter_map(|v| v(&value).err())
            .collect();

        if errors.is_empty() {
            Ok(value)
        } else {
            Err(errors)
        }
    }
}

impl<T: Default> Default for Builder<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// A simple event bus.
pub struct EventBus<E> {
    handlers: Arc<RwLock<Vec<Box<dyn Fn(&E) + Send + Sync>>>>,
}

impl<E> EventBus<E> {
    /// Create a new event bus.
    pub fn new() -> Self {
        Self {
            handlers: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// Subscribe to events.
    pub fn subscribe<F>(&self, handler: F)
    where
        F: Fn(&E) + Send + Sync + 'static,
    {
        if let Ok(mut handlers) = self.handlers.write() {
            handlers.push(Box::new(handler));
        }
    }

    /// Publish an event.
    pub fn publish(&self, event: &E) {
        if let Ok(handlers) = self.handlers.read() {
            for handler in handlers.iter() {
                handler(event);
            }
        }
    }
}

impl<E> Default for EventBus<E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E> Clone for EventBus<E> {
    fn clone(&self) -> Self {
        Self {
            handlers: Arc::clone(&self.handlers),
        }
    }
}

/// A rate limiter.
pub struct RateLimiter {
    permits: usize,
    window_ms: u64,
    requests: Mutex<VecDeque<u64>>,
}

impl RateLimiter {
    /// Create a new rate limiter.
    pub fn new(permits: usize, window_ms: u64) -> Self {
        Self {
            permits,
            window_ms,
            requests: Mutex::new(VecDeque::new()),
        }
    }

    /// Try to acquire a permit.
    pub fn try_acquire(&self) -> bool {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis() as u64;

        let mut requests = self.requests.lock().unwrap();

        // Remove expired requests
        while let Some(&oldest) = requests.front() {
            if now - oldest > self.window_ms {
                requests.pop_front();
            } else {
                break;
            }
        }

        if requests.len() < self.permits {
            requests.push_back(now);
            true
        } else {
            false
        }
    }

    /// Get remaining permits.
    pub fn remaining(&self) -> usize {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis() as u64;

        let requests = self.requests.lock().unwrap();
        let active = requests.iter().filter(|&&t| now - t <= self.window_ms).count();
        self.permits.saturating_sub(active)
    }
}

/// A simple retry policy.
#[derive(Debug, Clone)]
pub struct RetryPolicy {
    pub max_attempts: usize,
    pub initial_delay_ms: u64,
    pub max_delay_ms: u64,
    pub backoff_multiplier: f64,
}

impl RetryPolicy {
    /// Create a new retry policy.
    pub fn new(max_attempts: usize) -> Self {
        Self {
            max_attempts,
            initial_delay_ms: 100,
            max_delay_ms: 10000,
            backoff_multiplier: 2.0,
        }
    }

    /// Set initial delay.
    pub fn with_initial_delay(mut self, ms: u64) -> Self {
        self.initial_delay_ms = ms;
        self
    }

    /// Set max delay.
    pub fn with_max_delay(mut self, ms: u64) -> Self {
        self.max_delay_ms = ms;
        self
    }

    /// Set backoff multiplier.
    pub fn with_backoff(mut self, multiplier: f64) -> Self {
        self.backoff_multiplier = multiplier;
        self
    }

    /// Calculate delay for attempt.
    pub fn delay_for_attempt(&self, attempt: usize) -> u64 {
        let delay =
            self.initial_delay_ms as f64 * self.backoff_multiplier.powi(attempt as i32);
        (delay as u64).min(self.max_delay_ms)
    }
}

impl Default for RetryPolicy {
    fn default() -> Self {
        Self::new(3)
    }
}

/// A circuit breaker for fault tolerance.
pub struct CircuitBreaker {
    failure_threshold: usize,
    success_threshold: usize,
    timeout_ms: u64,
    state: Mutex<CircuitState>,
}

#[derive(Debug, Clone)]
enum CircuitState {
    Closed { failures: usize },
    Open { since: u64 },
    HalfOpen { successes: usize },
}

impl CircuitBreaker {
    /// Create a new circuit breaker.
    pub fn new(failure_threshold: usize, success_threshold: usize, timeout_ms: u64) -> Self {
        Self {
            failure_threshold,
            success_threshold,
            timeout_ms,
            state: Mutex::new(CircuitState::Closed { failures: 0 }),
        }
    }

    /// Check if a call is allowed.
    pub fn allow(&self) -> bool {
        let mut state = self.state.lock().unwrap();
        let now = self.now();

        match &*state {
            CircuitState::Closed { .. } => true,
            CircuitState::Open { since } => {
                if now - since >= self.timeout_ms {
                    *state = CircuitState::HalfOpen { successes: 0 };
                    true
                } else {
                    false
                }
            }
            CircuitState::HalfOpen { .. } => true,
        }
    }

    /// Record a success.
    pub fn record_success(&self) {
        let mut state = self.state.lock().unwrap();

        match &*state {
            CircuitState::Closed { .. } => {
                *state = CircuitState::Closed { failures: 0 };
            }
            CircuitState::HalfOpen { successes } => {
                if successes + 1 >= self.success_threshold {
                    *state = CircuitState::Closed { failures: 0 };
                } else {
                    *state = CircuitState::HalfOpen {
                        successes: successes + 1,
                    };
                }
            }
            CircuitState::Open { .. } => {}
        }
    }

    /// Record a failure.
    pub fn record_failure(&self) {
        let mut state = self.state.lock().unwrap();
        let now = self.now();

        match &*state {
            CircuitState::Closed { failures } => {
                if failures + 1 >= self.failure_threshold {
                    *state = CircuitState::Open { since: now };
                } else {
                    *state = CircuitState::Closed {
                        failures: failures + 1,
                    };
                }
            }
            CircuitState::HalfOpen { .. } => {
                *state = CircuitState::Open { since: now };
            }
            CircuitState::Open { .. } => {}
        }
    }

    /// Get current state name.
    pub fn state_name(&self) -> &'static str {
        let state = self.state.lock().unwrap();
        match &*state {
            CircuitState::Closed { .. } => "closed",
            CircuitState::Open { .. } => "open",
            CircuitState::HalfOpen { .. } => "half-open",
        }
    }

    fn now(&self) -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis() as u64
    }
}

/// A simple object pool.
pub struct ObjectPool<T> {
    objects: Mutex<Vec<T>>,
    factory: Box<dyn Fn() -> T + Send + Sync>,
    max_size: usize,
}

impl<T> ObjectPool<T> {
    /// Create a new object pool.
    pub fn new<F>(factory: F, max_size: usize) -> Self
    where
        F: Fn() -> T + Send + Sync + 'static,
    {
        Self {
            objects: Mutex::new(Vec::with_capacity(max_size)),
            factory: Box::new(factory),
            max_size,
        }
    }

    /// Acquire an object from the pool.
    pub fn acquire(&self) -> T {
        let mut objects = self.objects.lock().unwrap();
        objects.pop().unwrap_or_else(|| (self.factory)())
    }

    /// Return an object to the pool.
    pub fn release(&self, object: T) {
        let mut objects = self.objects.lock().unwrap();
        if objects.len() < self.max_size {
            objects.push(object);
        }
    }

    /// Get the current pool size.
    pub fn size(&self) -> usize {
        self.objects.lock().unwrap().len()
    }
}

/// A simple bloom filter.
pub struct BloomFilter {
    bits: Vec<bool>,
    hash_count: usize,
}

impl BloomFilter {
    /// Create a new bloom filter.
    pub fn new(size: usize, hash_count: usize) -> Self {
        Self {
            bits: vec![false; size],
            hash_count,
        }
    }

    /// Add an item to the filter.
    pub fn add(&mut self, item: &[u8]) {
        for i in 0..self.hash_count {
            let idx = self.hash(item, i) % self.bits.len();
            self.bits[idx] = true;
        }
    }

    /// Check if an item might be in the filter.
    pub fn might_contain(&self, item: &[u8]) -> bool {
        for i in 0..self.hash_count {
            let idx = self.hash(item, i) % self.bits.len();
            if !self.bits[idx] {
                return false;
            }
        }
        true
    }

    /// Clear the filter.
    pub fn clear(&mut self) {
        self.bits.fill(false);
    }

    fn hash(&self, item: &[u8], seed: usize) -> usize {
        let mut h: usize = seed.wrapping_mul(0x9e3779b9);
        for &byte in item {
            h = h.wrapping_mul(31).wrapping_add(byte as usize);
        }
        h
    }
}

/// A trie (prefix tree) for string keys.
pub struct Trie<V> {
    root: TrieNode<V>,
}

struct TrieNode<V> {
    children: HashMap<char, TrieNode<V>>,
    value: Option<V>,
}

impl<V> Trie<V> {
    /// Create a new trie.
    pub fn new() -> Self {
        Self {
            root: TrieNode::new(),
        }
    }

    /// Insert a key-value pair.
    pub fn insert(&mut self, key: &str, value: V) {
        let mut node = &mut self.root;
        for ch in key.chars() {
            node = node.children.entry(ch).or_insert_with(TrieNode::new);
        }
        node.value = Some(value);
    }

    /// Get a value by key.
    pub fn get(&self, key: &str) -> Option<&V> {
        let mut node = &self.root;
        for ch in key.chars() {
            node = node.children.get(&ch)?;
        }
        node.value.as_ref()
    }

    /// Get a mutable reference to a value.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut V> {
        let mut node = &mut self.root;
        for ch in key.chars() {
            node = node.children.get_mut(&ch)?;
        }
        node.value.as_mut()
    }

    /// Check if a key exists.
    pub fn contains(&self, key: &str) -> bool {
        self.get(key).is_some()
    }

    /// Check if any key starts with the given prefix.
    pub fn starts_with(&self, prefix: &str) -> bool {
        let mut node = &self.root;
        for ch in prefix.chars() {
            match node.children.get(&ch) {
                Some(n) => node = n,
                None => return false,
            }
        }
        true
    }

    /// Get all keys with the given prefix.
    pub fn keys_with_prefix(&self, prefix: &str) -> Vec<String> {
        let mut result = Vec::new();
        let mut node = &self.root;

        for ch in prefix.chars() {
            match node.children.get(&ch) {
                Some(n) => node = n,
                None => return result,
            }
        }

        self.collect_keys(node, prefix.to_string(), &mut result);
        result
    }

    fn collect_keys(&self, node: &TrieNode<V>, current: String, result: &mut Vec<String>) {
        if node.value.is_some() {
            result.push(current.clone());
        }
        for (&ch, child) in &node.children {
            let mut next = current.clone();
            next.push(ch);
            self.collect_keys(child, next, result);
        }
    }
}

impl<V> TrieNode<V> {
    fn new() -> Self {
        Self {
            children: HashMap::new(),
            value: None,
        }
    }
}

impl<V> Default for Trie<V> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_point_operations() {
        let p1 = Point::new(3.0, 4.0);
        let p2 = Point::new(0.0, 0.0);
        assert!((p1.distance_to(&p2) - 5.0).abs() < 1e-10);
    }

    #[test]
    fn test_rectangle_contains() {
        let rect = Rectangle::new(Point::new(0.0, 0.0), Point::new(10.0, 10.0));
        assert!(rect.contains(&Point::new(5.0, 5.0)));
        assert!(!rect.contains(&Point::new(15.0, 5.0)));
    }

    #[test]
    fn test_lru_cache() {
        let mut cache = LruCache::new(2);
        cache.insert("a", 1);
        cache.insert("b", 2);
        assert_eq!(cache.get(&"a"), Some(&1));
        cache.insert("c", 3);
        assert_eq!(cache.get(&"b"), None);
    }

    #[test]
    fn test_counter() {
        let counter = Counter::new();
        assert_eq!(counter.get(), 0);
        assert_eq!(counter.increment(), 1);
        assert_eq!(counter.increment(), 2);
        counter.reset();
        assert_eq!(counter.get(), 0);
    }

    #[test]
    fn test_trie() {
        let mut trie = Trie::new();
        trie.insert("hello", 1);
        trie.insert("help", 2);
        trie.insert("world", 3);

        assert_eq!(trie.get("hello"), Some(&1));
        assert!(trie.starts_with("hel"));
        assert!(!trie.starts_with("wor"));
    }
}
