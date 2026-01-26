//! Comprehensive AST extraction benchmarks.
//!
//! This module provides detailed performance benchmarks for AST extraction
//! across multiple programming languages, measuring:
//!
//! - Function extraction performance (various complexity levels)
//! - Class/struct extraction performance
//! - Scaling behavior (small, medium, large files)
//! - Parse time vs extraction time breakdown
//!
//! Run with: `cargo bench --bench ast_extraction`

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use brrr::ast::extractor::AstExtractor;
use brrr::lang::LanguageRegistry;

// =============================================================================
// Test Code Generators
// =============================================================================

/// Generate Python code with various function patterns.
mod python_generators {
    /// Simple function without decorators.
    pub fn simple_function() -> &'static str {
        r#"
def add(a: int, b: int) -> int:
    """Add two numbers together."""
    return a + b
"#
    }

    /// Function with decorators.
    pub fn decorated_function() -> &'static str {
        r#"
@staticmethod
@cache
@log_execution(level="debug")
def process_data(data: list[dict], config: Config) -> ProcessResult:
    """Process data according to configuration.

    Args:
        data: Input data to process.
        config: Processing configuration.

    Returns:
        ProcessResult with status and output.
    """
    result = []
    for item in data:
        transformed = transform(item, config)
        result.append(transformed)
    return ProcessResult(status="ok", data=result)
"#
    }

    /// Async function.
    pub fn async_function() -> &'static str {
        r#"
async def fetch_data(url: str, timeout: float = 30.0) -> bytes:
    """Fetch data from a URL asynchronously.

    Args:
        url: The URL to fetch from.
        timeout: Request timeout in seconds.

    Returns:
        Response body as bytes.

    Raises:
        TimeoutError: If request times out.
        ConnectionError: If connection fails.
    """
    async with aiohttp.ClientSession() as session:
        async with session.get(url, timeout=timeout) as response:
            response.raise_for_status()
            return await response.read()
"#
    }

    /// Nested functions.
    pub fn nested_function() -> &'static str {
        r#"
def outer_function(x: int) -> Callable[[int], int]:
    """Create a closure that adds x to its argument.

    Args:
        x: The value to capture in the closure.

    Returns:
        A function that adds x to its input.
    """
    captured_value = x * 2

    def inner_function(y: int) -> int:
        """Inner function that uses captured value."""
        return captured_value + y

    def another_inner(z: int) -> int:
        """Another nested function."""
        return inner_function(z) * 2

    return another_inner
"#
    }

    /// Class with methods and docstrings.
    pub fn class_with_methods() -> &'static str {
        r#"
class DataProcessor:
    """A class for processing data with various transformations.

    This class provides methods for loading, transforming, and saving data
    with configurable options and validation.

    Attributes:
        config: The processor configuration.
        logger: Logger instance for tracking operations.
    """

    def __init__(self, config: ProcessorConfig, logger: Logger | None = None):
        """Initialize the data processor.

        Args:
            config: Configuration for the processor.
            logger: Optional logger instance.
        """
        self.config = config
        self.logger = logger or get_default_logger()
        self._cache: dict[str, Any] = {}

    def load(self, path: str) -> Data:
        """Load data from a file path.

        Args:
            path: Path to the data file.

        Returns:
            Loaded data object.

        Raises:
            FileNotFoundError: If path doesn't exist.
            ParseError: If file format is invalid.
        """
        self.logger.info(f"Loading data from {path}")
        with open(path, 'rb') as f:
            return self._parse(f.read())

    def transform(self, data: Data, rules: list[Rule]) -> Data:
        """Apply transformation rules to data.

        Args:
            data: Input data to transform.
            rules: List of transformation rules.

        Returns:
            Transformed data object.
        """
        result = data
        for rule in rules:
            result = rule.apply(result)
            if self.config.validate_intermediate:
                self._validate(result)
        return result

    @staticmethod
    def validate(data: Data) -> ValidationResult:
        """Validate data structure and content.

        Args:
            data: Data to validate.

        Returns:
            Validation result with errors if any.
        """
        errors = []
        if not data.has_required_fields():
            errors.append("Missing required fields")
        if not data.is_consistent():
            errors.append("Data inconsistency detected")
        return ValidationResult(valid=len(errors) == 0, errors=errors)

    @classmethod
    def from_json(cls, json_str: str) -> 'DataProcessor':
        """Create processor from JSON configuration.

        Args:
            json_str: JSON configuration string.

        Returns:
            New DataProcessor instance.
        """
        config = ProcessorConfig.from_json(json_str)
        return cls(config)

    async def process_async(self, data: Data) -> ProcessResult:
        """Asynchronously process data.

        Args:
            data: Data to process.

        Returns:
            Processing result.
        """
        validated = self.validate(data)
        if not validated.valid:
            raise ValidationError(validated.errors)
        return await self._do_async_processing(data)

    def _parse(self, raw: bytes) -> Data:
        """Internal parsing method."""
        return Data.parse(raw, self.config.format)

    def _validate(self, data: Data) -> None:
        """Internal validation helper."""
        result = self.validate(data)
        if not result.valid:
            raise ValidationError(result.errors)
"#
    }

    /// Generate Python code with N functions.
    pub fn generate_n_functions(n: usize) -> String {
        let mut code = String::with_capacity(n * 200);
        for i in 0..n {
            code.push_str(&format!(
                r#"
def function_{i}(x: int, y: str, z: float = 0.0) -> dict[str, Any]:
    """Function number {i} for testing.

    Args:
        x: An integer parameter.
        y: A string parameter.
        z: An optional float parameter.

    Returns:
        A dictionary with results.
    """
    result = {{"x": x, "y": y, "z": z, "id": {i}}}
    if x > 0:
        result["positive"] = True
    return result

"#,
                i = i
            ));
        }
        code
    }

    /// Generate Python code with N classes.
    pub fn generate_n_classes(n: usize) -> String {
        let mut code = String::with_capacity(n * 500);
        for i in 0..n {
            code.push_str(&format!(
                r#"
class TestClass{i}:
    """Test class number {i}."""

    def __init__(self, value: int):
        """Initialize with value."""
        self.value = value
        self._cache: dict = {{}}

    def get_value(self) -> int:
        """Get the stored value."""
        return self.value

    def set_value(self, new_value: int) -> None:
        """Set a new value."""
        self.value = new_value
        self._cache.clear()

    @property
    def doubled(self) -> int:
        """Return doubled value."""
        return self.value * 2

"#,
                i = i
            ));
        }
        code
    }
}

/// Generate TypeScript code with various patterns.
mod typescript_generators {
    /// Arrow function.
    pub fn arrow_function() -> &'static str {
        r#"
const add = (a: number, b: number): number => a + b;

const processItems = async <T extends Item>(
    items: T[],
    options: ProcessOptions
): Promise<ProcessResult<T>> => {
    const results: T[] = [];
    for (const item of items) {
        const processed = await processItem(item, options);
        results.push(processed);
    }
    return { items: results, count: results.length };
};
"#
    }

    /// Async function with generics.
    pub fn async_function() -> &'static str {
        r#"
async function fetchData<T>(
    url: string,
    options?: RequestOptions
): Promise<ApiResponse<T>> {
    const response = await fetch(url, {
        method: options?.method ?? 'GET',
        headers: {
            'Content-Type': 'application/json',
            ...options?.headers,
        },
        body: options?.body ? JSON.stringify(options.body) : undefined,
    });

    if (!response.ok) {
        throw new ApiError(response.status, await response.text());
    }

    return response.json();
}
"#
    }

    /// Generator function.
    pub fn generator_function() -> &'static str {
        r#"
function* fibonacci(limit: number): Generator<number, void, unknown> {
    let [prev, curr] = [0, 1];
    while (curr < limit) {
        yield curr;
        [prev, curr] = [curr, prev + curr];
    }
}

async function* asyncPaginate<T>(
    fetcher: (page: number) => Promise<Page<T>>
): AsyncGenerator<T, void, unknown> {
    let page = 0;
    let hasMore = true;

    while (hasMore) {
        const result = await fetcher(page);
        for (const item of result.items) {
            yield item;
        }
        hasMore = result.hasNext;
        page++;
    }
}
"#
    }

    /// Class with decorators and getters/setters.
    pub fn class_with_decorators() -> &'static str {
        r#"
@Injectable()
@Component({
    selector: 'app-user-profile',
    template: '<div>{{ user.name }}</div>',
})
export class UserProfileComponent implements OnInit, OnDestroy {
    private _user: User | null = null;
    private subscription: Subscription | null = null;

    @Input()
    set user(value: User | null) {
        this._user = value;
        this.updateView();
    }

    get user(): User | null {
        return this._user;
    }

    @Output()
    readonly userChanged = new EventEmitter<User>();

    constructor(
        private userService: UserService,
        @Inject(CONFIG_TOKEN) private config: AppConfig
    ) {}

    ngOnInit(): void {
        this.subscription = this.userService.currentUser$.subscribe(
            user => this.user = user
        );
    }

    ngOnDestroy(): void {
        this.subscription?.unsubscribe();
    }

    @HostListener('click', ['$event'])
    onClick(event: MouseEvent): void {
        event.preventDefault();
        this.userChanged.emit(this._user!);
    }

    private updateView(): void {
        if (this._user) {
            console.log(`User updated: ${this._user.name}`);
        }
    }
}
"#
    }

    /// Generate TypeScript code with N functions.
    pub fn generate_n_functions(n: usize) -> String {
        let mut code = String::with_capacity(n * 300);
        for i in 0..n {
            code.push_str(&format!(
                r#"
/**
 * Function number {i} for testing.
 * @param x - A number parameter
 * @param y - A string parameter
 * @param options - Optional configuration
 * @returns Object with results
 */
export function function{i}(
    x: number,
    y: string,
    options?: {{ debug?: boolean; timeout?: number }}
): Record<string, unknown> {{
    const result: Record<string, unknown> = {{
        x,
        y,
        id: {i},
        timestamp: Date.now(),
    }};

    if (options?.debug) {{
        console.log(`function{i} called with x=${{x}}, y=${{y}}`);
    }}

    return result;
}}

"#,
                i = i
            ));
        }
        code
    }
}

/// Generate Rust code with various patterns.
mod rust_generators {
    /// Generic function with lifetimes.
    pub fn generic_function() -> &'static str {
        r#"
/// Process items with a transformation function.
///
/// # Type Parameters
///
/// * `T` - Input item type
/// * `U` - Output item type
/// * `F` - Transformation function type
///
/// # Arguments
///
/// * `items` - Slice of items to process
/// * `transform` - Function to apply to each item
///
/// # Returns
///
/// Vector of transformed items.
pub fn process<T, U, F>(items: &[T], transform: F) -> Vec<U>
where
    T: Clone,
    U: Default,
    F: Fn(&T) -> U,
{
    items.iter().map(transform).collect()
}

/// Find item with lifetime tracking.
pub fn find_first<'a, T, P>(items: &'a [T], predicate: P) -> Option<&'a T>
where
    P: Fn(&T) -> bool,
{
    items.iter().find(|item| predicate(item))
}
"#
    }

    /// Async function with error handling.
    pub fn async_function() -> &'static str {
        r#"
/// Fetch data from a URL asynchronously.
///
/// # Arguments
///
/// * `client` - HTTP client to use
/// * `url` - URL to fetch from
/// * `timeout` - Request timeout duration
///
/// # Returns
///
/// Response bytes on success.
///
/// # Errors
///
/// Returns error if request fails or times out.
pub async fn fetch_data(
    client: &Client,
    url: &str,
    timeout: Duration,
) -> Result<Vec<u8>, FetchError> {
    let response = tokio::time::timeout(
        timeout,
        client.get(url).send()
    )
    .await
    .map_err(|_| FetchError::Timeout)?
    .map_err(FetchError::Request)?;

    if !response.status().is_success() {
        return Err(FetchError::Status(response.status()));
    }

    response.bytes()
        .await
        .map(|b| b.to_vec())
        .map_err(FetchError::Body)
}
"#
    }

    /// Struct with impl blocks.
    pub fn struct_with_impl() -> &'static str {
        r#"
/// A processor for transforming data.
///
/// This struct handles data transformation with configurable
/// options and caching support.
#[derive(Debug, Clone)]
pub struct DataProcessor<T: Clone> {
    /// Configuration for the processor
    config: ProcessorConfig,
    /// Cached results
    cache: HashMap<String, T>,
    /// Processing statistics
    stats: ProcessorStats,
}

impl<T: Clone> DataProcessor<T> {
    /// Create a new processor with configuration.
    ///
    /// # Arguments
    ///
    /// * `config` - Processor configuration
    ///
    /// # Returns
    ///
    /// New `DataProcessor` instance.
    pub fn new(config: ProcessorConfig) -> Self {
        Self {
            config,
            cache: HashMap::new(),
            stats: ProcessorStats::default(),
        }
    }

    /// Process data with transformation.
    pub fn process(&mut self, data: &T, key: &str) -> Result<T, ProcessError> {
        if let Some(cached) = self.cache.get(key) {
            self.stats.cache_hits += 1;
            return Ok(cached.clone());
        }

        self.stats.cache_misses += 1;
        let result = self.transform(data)?;
        self.cache.insert(key.to_string(), result.clone());
        Ok(result)
    }

    fn transform(&self, data: &T) -> Result<T, ProcessError> {
        // Transform implementation
        Ok(data.clone())
    }
}

impl<T: Clone + Default> Default for DataProcessor<T> {
    fn default() -> Self {
        Self::new(ProcessorConfig::default())
    }
}
"#
    }

    /// Enum with methods.
    pub fn enum_with_methods() -> &'static str {
        r#"
/// Result status for operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Status {
    /// Operation succeeded
    Success,
    /// Operation failed with error
    Error(String),
    /// Operation is pending
    Pending { progress: u8 },
    /// Operation was cancelled
    Cancelled,
}

impl Status {
    /// Check if status represents success.
    pub fn is_success(&self) -> bool {
        matches!(self, Status::Success)
    }

    /// Check if status represents failure.
    pub fn is_error(&self) -> bool {
        matches!(self, Status::Error(_))
    }

    /// Get error message if status is error.
    pub fn error_message(&self) -> Option<&str> {
        match self {
            Status::Error(msg) => Some(msg),
            _ => None,
        }
    }

    /// Get progress if status is pending.
    pub fn progress(&self) -> Option<u8> {
        match self {
            Status::Pending { progress } => Some(*progress),
            _ => None,
        }
    }
}

impl Default for Status {
    fn default() -> Self {
        Status::Pending { progress: 0 }
    }
}
"#
    }

    /// Trait definition.
    pub fn trait_definition() -> &'static str {
        r#"
/// Trait for types that can be processed.
pub trait Processable: Send + Sync {
    /// The output type after processing.
    type Output;

    /// The error type for processing failures.
    type Error: std::error::Error;

    /// Process the item.
    fn process(&self) -> Result<Self::Output, Self::Error>;

    /// Check if item can be processed.
    fn can_process(&self) -> bool {
        true
    }

    /// Get processing priority.
    fn priority(&self) -> u32 {
        0
    }
}

/// Trait for async processing.
#[async_trait]
pub trait AsyncProcessable: Send + Sync {
    type Output: Send;
    type Error: std::error::Error + Send;

    async fn process_async(&self) -> Result<Self::Output, Self::Error>;
}
"#
    }

    /// Generate Rust code with N functions.
    pub fn generate_n_functions(n: usize) -> String {
        let mut code = String::with_capacity(n * 400);
        for i in 0..n {
            code.push_str(&format!(
                r#"
/// Function number {i} for testing.
///
/// # Arguments
///
/// * `x` - Integer input
/// * `y` - String input
/// * `z` - Optional float input
///
/// # Returns
///
/// HashMap with results.
pub fn function_{i}(
    x: i32,
    y: &str,
    z: Option<f64>,
) -> HashMap<String, Value> {{
    let mut result = HashMap::new();
    result.insert("x".to_string(), Value::Int(x));
    result.insert("y".to_string(), Value::String(y.to_string()));
    result.insert("id".to_string(), Value::Int({i}));

    if let Some(z_val) = z {{
        result.insert("z".to_string(), Value::Float(z_val));
    }}

    if x > 0 {{
        result.insert("positive".to_string(), Value::Bool(true));
    }}

    result
}}

"#,
                i = i
            ));
        }
        code
    }
}

/// Generate Go code with various patterns.
mod go_generators {
    /// Function with receiver (method).
    pub fn method_with_receiver() -> &'static str {
        r#"
package main

// Process processes the data with the given configuration.
// It returns the processed result or an error if processing fails.
func (p *Processor) Process(data []byte, config *Config) (*Result, error) {
    if data == nil {
        return nil, ErrNilData
    }

    parsed, err := p.parse(data)
    if err != nil {
        return nil, fmt.Errorf("failed to parse data: %w", err)
    }

    transformed := p.transform(parsed, config)

    return &Result{
        Data:      transformed,
        Timestamp: time.Now(),
    }, nil
}

// GetStatus returns the current processor status.
func (p *Processor) GetStatus() Status {
    p.mu.RLock()
    defer p.mu.RUnlock()
    return p.status
}
"#
    }

    /// Struct type declaration.
    pub fn struct_definition() -> &'static str {
        r#"
package main

// Processor handles data processing operations.
// It supports concurrent processing with configurable workers.
type Processor struct {
    config  *Config
    workers int
    mu      sync.RWMutex
    status  Status
    cache   map[string][]byte
}

// Config holds processor configuration.
type Config struct {
    MaxSize     int
    Timeout     time.Duration
    Retries     int
    Debug       bool
    Compression CompressionType
}

// Result represents a processing result.
type Result struct {
    Data      []byte
    Timestamp time.Time
    Duration  time.Duration
    Status    Status
}
"#
    }

    /// Interface definition.
    pub fn interface_definition() -> &'static str {
        r#"
package main

// Handler handles requests and responses.
type Handler interface {
    // Handle processes a request and returns a response.
    Handle(ctx context.Context, req *Request) (*Response, error)

    // CanHandle checks if this handler can process the request.
    CanHandle(req *Request) bool
}

// Processor defines the processing interface.
type Processor interface {
    Handler

    // Process transforms input data.
    Process(data []byte) ([]byte, error)

    // Status returns current processor status.
    Status() Status
}
"#
    }

    /// Generate Go code with N functions.
    pub fn generate_n_functions(n: usize) -> String {
        let mut code = String::with_capacity(n * 300);
        code.push_str("package main\n\n");
        for i in 0..n {
            code.push_str(&format!(
                r#"
// Function{i} processes input and returns a result.
// It handles various edge cases and validates input.
func Function{i}(x int, y string, z float64) (map[string]interface{{}}, error) {{
    result := make(map[string]interface{{}})
    result["x"] = x
    result["y"] = y
    result["z"] = z
    result["id"] = {i}

    if x < 0 {{
        return nil, fmt.Errorf("x must be non-negative, got %d", x)
    }}

    if x > 0 {{
        result["positive"] = true
    }}

    return result, nil
}}

"#,
                i = i
            ));
        }
        code
    }
}

/// Generate Java code with various patterns.
mod java_generators {
    /// Method with annotations.
    pub fn annotated_method() -> &'static str {
        r##"
package com.example.service;

import java.util.*;
import javax.annotation.*;

public class UserService {

    /**
     * Process user data with validation.
     *
     * @param user the user to process
     * @param options processing options
     * @return the processing result
     * @throws ValidationException if validation fails
     */
    @Override
    @Transactional(readOnly = false)
    @Cacheable(value = "users", key = "#user.id")
    public ProcessResult processUser(
            @NonNull User user,
            @Nullable ProcessOptions options) throws ValidationException {

        Objects.requireNonNull(user, "User cannot be null");

        if (!validator.validate(user)) {
            throw new ValidationException("User validation failed");
        }

        User processed = transformer.transform(user, options);
        repository.save(processed);

        return new ProcessResult(processed, Status.SUCCESS);
    }

    /**
     * Find user by ID.
     *
     * @param id the user ID
     * @return optional containing the user if found
     */
    @Cacheable(value = "users", key = "#id")
    public Optional<User> findById(@NonNull Long id) {
        return repository.findById(id);
    }
}
"##
    }

    /// Class with generics and inner classes.
    pub fn generic_class() -> &'static str {
        r#"
package com.example.collections;

import java.util.*;
import java.util.function.*;

/**
 * A generic container with transformation support.
 *
 * @param <T> the type of elements
 */
public class Container<T extends Comparable<T>> implements Iterable<T> {

    private final List<T> elements;
    private final Comparator<T> comparator;

    /**
     * Creates a new container with the given elements.
     *
     * @param elements initial elements
     */
    public Container(Collection<T> elements) {
        this.elements = new ArrayList<>(elements);
        this.comparator = Comparator.naturalOrder();
    }

    /**
     * Transform all elements using the given function.
     *
     * @param <U> the output type
     * @param mapper transformation function
     * @return new container with transformed elements
     */
    public <U extends Comparable<U>> Container<U> map(Function<T, U> mapper) {
        List<U> mapped = new ArrayList<>();
        for (T element : elements) {
            mapped.add(mapper.apply(element));
        }
        return new Container<>(mapped);
    }

    /**
     * Filter elements by predicate.
     *
     * @param predicate filter condition
     * @return new container with filtered elements
     */
    public Container<T> filter(Predicate<T> predicate) {
        List<T> filtered = new ArrayList<>();
        for (T element : elements) {
            if (predicate.test(element)) {
                filtered.add(element);
            }
        }
        return new Container<>(filtered);
    }

    @Override
    public Iterator<T> iterator() {
        return elements.iterator();
    }

    /**
     * Builder for Container instances.
     *
     * @param <T> element type
     */
    public static class Builder<T extends Comparable<T>> {
        private final List<T> elements = new ArrayList<>();

        public Builder<T> add(T element) {
            elements.add(element);
            return this;
        }

        public Builder<T> addAll(Collection<T> elements) {
            this.elements.addAll(elements);
            return this;
        }

        public Container<T> build() {
            return new Container<>(elements);
        }
    }
}
"#
    }

    /// Generate Java code with N methods.
    pub fn generate_n_methods(n: usize) -> String {
        let mut code = String::with_capacity(n * 400);
        code.push_str("package com.example.generated;\n\n");
        code.push_str("import java.util.*;\n\n");
        code.push_str("public class GeneratedService {\n\n");

        for i in 0..n {
            code.push_str(&format!(
                r#"    /**
     * Method number {i} for testing.
     *
     * @param x integer parameter
     * @param y string parameter
     * @param z optional double parameter
     * @return map with results
     */
    public Map<String, Object> method{i}(int x, String y, Double z) {{
        Map<String, Object> result = new HashMap<>();
        result.put("x", x);
        result.put("y", y);
        result.put("id", {i});

        if (z != null) {{
            result.put("z", z);
        }}

        if (x > 0) {{
            result.put("positive", true);
        }}

        return result;
    }}

"#,
                i = i
            ));
        }

        code.push_str("}\n");
        code
    }
}

/// Generate C code with various patterns.
mod c_generators {
    /// Function with macros.
    pub fn function_with_macros() -> &'static str {
        r#"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_BUFFER_SIZE 4096
#define CHECK_NULL(ptr) if ((ptr) == NULL) return -1

/**
 * Process data buffer with transformation.
 *
 * @param input Input buffer
 * @param input_size Size of input buffer
 * @param output Output buffer (must be pre-allocated)
 * @param output_size Pointer to output size (in/out)
 * @return 0 on success, negative on error
 */
int process_buffer(
    const unsigned char *input,
    size_t input_size,
    unsigned char *output,
    size_t *output_size
) {
    CHECK_NULL(input);
    CHECK_NULL(output);
    CHECK_NULL(output_size);

    if (input_size > MAX_BUFFER_SIZE) {
        return -1;
    }

    size_t processed = 0;
    for (size_t i = 0; i < input_size; i++) {
        output[processed++] = transform_byte(input[i]);
    }

    *output_size = processed;
    return 0;
}

/**
 * Allocate and initialize a new processor.
 *
 * @param config Configuration options
 * @return Pointer to processor or NULL on failure
 */
processor_t *processor_create(const config_t *config) {
    processor_t *proc = malloc(sizeof(processor_t));
    if (proc == NULL) {
        return NULL;
    }

    memset(proc, 0, sizeof(processor_t));
    proc->config = *config;
    proc->status = STATUS_INITIALIZED;

    return proc;
}
"#
    }

    /// Struct with bitfields.
    pub fn struct_with_bitfields() -> &'static str {
        r#"
#include <stdint.h>

/**
 * Flags for packet header.
 */
typedef struct {
    uint8_t version : 4;
    uint8_t type : 4;
    uint8_t flags : 8;
    uint16_t length;
} packet_header_t;

/**
 * Processor state structure.
 */
typedef struct processor {
    config_t config;
    status_t status;
    uint32_t processed_count;
    uint32_t error_count;
    void *user_data;

    /* Function pointers */
    int (*transform)(const void *, void *, size_t);
    void (*cleanup)(struct processor *);
} processor_t;

/**
 * Initialize processor with default configuration.
 *
 * @param proc Processor to initialize
 * @return 0 on success
 */
int processor_init(processor_t *proc);

/**
 * Destroy processor and free resources.
 *
 * @param proc Processor to destroy
 */
void processor_destroy(processor_t *proc);
"#
    }
}

/// Generate C++ code with various patterns.
mod cpp_generators {
    /// Class with templates.
    pub fn template_class() -> &'static str {
        r#"
#include <memory>
#include <vector>
#include <functional>

namespace processing {

/**
 * @brief A generic processor for transforming data.
 *
 * @tparam T Input type
 * @tparam U Output type
 */
template<typename T, typename U>
class Processor {
public:
    using TransformFunc = std::function<U(const T&)>;
    using FilterFunc = std::function<bool(const T&)>;

    /**
     * @brief Construct a new Processor.
     *
     * @param transform Transformation function
     */
    explicit Processor(TransformFunc transform)
        : transform_(std::move(transform))
        , filter_([](const T&) { return true; })
    {}

    /**
     * @brief Set filter function.
     *
     * @param filter Filter predicate
     * @return Reference to this for chaining
     */
    Processor& setFilter(FilterFunc filter) {
        filter_ = std::move(filter);
        return *this;
    }

    /**
     * @brief Process a vector of items.
     *
     * @param items Input items
     * @return Vector of processed items
     */
    std::vector<U> process(const std::vector<T>& items) const {
        std::vector<U> results;
        results.reserve(items.size());

        for (const auto& item : items) {
            if (filter_(item)) {
                results.push_back(transform_(item));
            }
        }

        return results;
    }

private:
    TransformFunc transform_;
    FilterFunc filter_;
};

/**
 * @brief Factory for creating processors.
 */
template<typename T, typename U>
class ProcessorFactory {
public:
    /**
     * @brief Create a processor with the given transform.
     *
     * @param transform Transform function
     * @return Unique pointer to processor
     */
    static std::unique_ptr<Processor<T, U>> create(
        typename Processor<T, U>::TransformFunc transform
    ) {
        return std::make_unique<Processor<T, U>>(std::move(transform));
    }
};

} // namespace processing
"#
    }

    /// Class with inheritance.
    pub fn class_with_inheritance() -> &'static str {
        r#"
#include <string>
#include <memory>

/**
 * @brief Base handler interface.
 */
class IHandler {
public:
    virtual ~IHandler() = default;

    /**
     * @brief Handle a request.
     *
     * @param request Request data
     * @return Response data
     */
    virtual std::string handle(const std::string& request) = 0;

    /**
     * @brief Check if handler can process request.
     *
     * @param request Request to check
     * @return true if can handle
     */
    virtual bool canHandle(const std::string& request) const = 0;
};

/**
 * @brief Base implementation with common functionality.
 */
class BaseHandler : public IHandler {
public:
    explicit BaseHandler(std::string name)
        : name_(std::move(name))
    {}

    bool canHandle(const std::string& request) const override {
        return !request.empty();
    }

protected:
    std::string name_;

    void log(const std::string& message) const {
        std::cout << "[" << name_ << "] " << message << std::endl;
    }
};

/**
 * @brief Specialized handler for JSON requests.
 */
class JsonHandler : public BaseHandler {
public:
    JsonHandler() : BaseHandler("JsonHandler") {}

    std::string handle(const std::string& request) override {
        log("Processing JSON request");
        // Parse and process JSON
        return "{ \"status\": \"ok\" }";
    }

    bool canHandle(const std::string& request) const override {
        return BaseHandler::canHandle(request) &&
               request.find('{') != std::string::npos;
    }
};
"#
    }
}

// =============================================================================
// Benchmark Groups
// =============================================================================

/// Benchmarks for Python function extraction.
fn bench_python_functions(c: &mut Criterion) {
    let mut group = c.benchmark_group("python_functions");

    // Simple function
    let simple = python_generators::simple_function();
    group.throughput(Throughput::Bytes(simple.len() as u64));
    group.bench_function("simple", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(simple, "python").unwrap()))
    });

    // Decorated function
    let decorated = python_generators::decorated_function();
    group.throughput(Throughput::Bytes(decorated.len() as u64));
    group.bench_function("decorated", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(decorated, "python").unwrap()))
    });

    // Async function
    let async_fn = python_generators::async_function();
    group.throughput(Throughput::Bytes(async_fn.len() as u64));
    group.bench_function("async", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(async_fn, "python").unwrap()))
    });

    // Nested function
    let nested = python_generators::nested_function();
    group.throughput(Throughput::Bytes(nested.len() as u64));
    group.bench_function("nested", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(nested, "python").unwrap()))
    });

    group.finish();
}

/// Benchmarks for Python class extraction.
fn bench_python_classes(c: &mut Criterion) {
    let mut group = c.benchmark_group("python_classes");

    let class_code = python_generators::class_with_methods();
    group.throughput(Throughput::Bytes(class_code.len() as u64));
    group.bench_function("class_with_methods", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(class_code, "python").unwrap()))
    });

    group.finish();
}

/// Benchmarks for TypeScript function extraction.
fn bench_typescript_functions(c: &mut Criterion) {
    let mut group = c.benchmark_group("typescript_functions");

    // Arrow function
    let arrow = typescript_generators::arrow_function();
    group.throughput(Throughput::Bytes(arrow.len() as u64));
    group.bench_function("arrow", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(arrow, "typescript").unwrap()))
    });

    // Async function
    let async_fn = typescript_generators::async_function();
    group.throughput(Throughput::Bytes(async_fn.len() as u64));
    group.bench_function("async", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(async_fn, "typescript").unwrap()))
    });

    // Generator function
    let generator = typescript_generators::generator_function();
    group.throughput(Throughput::Bytes(generator.len() as u64));
    group.bench_function("generator", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(generator, "typescript").unwrap()))
    });

    group.finish();
}

/// Benchmarks for TypeScript class extraction.
fn bench_typescript_classes(c: &mut Criterion) {
    let mut group = c.benchmark_group("typescript_classes");

    let decorated_class = typescript_generators::class_with_decorators();
    group.throughput(Throughput::Bytes(decorated_class.len() as u64));
    group.bench_function("decorated_class", |b| {
        b.iter(|| {
            black_box(AstExtractor::extract_from_source(decorated_class, "typescript").unwrap())
        })
    });

    group.finish();
}

/// Benchmarks for Rust function extraction.
fn bench_rust_functions(c: &mut Criterion) {
    let mut group = c.benchmark_group("rust_functions");

    // Generic function with lifetimes
    let generic = rust_generators::generic_function();
    group.throughput(Throughput::Bytes(generic.len() as u64));
    group.bench_function("generic_with_lifetimes", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(generic, "rust").unwrap()))
    });

    // Async function
    let async_fn = rust_generators::async_function();
    group.throughput(Throughput::Bytes(async_fn.len() as u64));
    group.bench_function("async", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(async_fn, "rust").unwrap()))
    });

    group.finish();
}

/// Benchmarks for Rust struct/enum/trait extraction.
fn bench_rust_types(c: &mut Criterion) {
    let mut group = c.benchmark_group("rust_types");

    // Struct with impl
    let struct_impl = rust_generators::struct_with_impl();
    group.throughput(Throughput::Bytes(struct_impl.len() as u64));
    group.bench_function("struct_with_impl", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(struct_impl, "rust").unwrap()))
    });

    // Enum with methods
    let enum_methods = rust_generators::enum_with_methods();
    group.throughput(Throughput::Bytes(enum_methods.len() as u64));
    group.bench_function("enum_with_methods", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(enum_methods, "rust").unwrap()))
    });

    // Trait definition
    let trait_def = rust_generators::trait_definition();
    group.throughput(Throughput::Bytes(trait_def.len() as u64));
    group.bench_function("trait_definition", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(trait_def, "rust").unwrap()))
    });

    group.finish();
}

/// Benchmarks for Go function extraction.
fn bench_go_functions(c: &mut Criterion) {
    let mut group = c.benchmark_group("go_functions");

    // Method with receiver
    let method = go_generators::method_with_receiver();
    group.throughput(Throughput::Bytes(method.len() as u64));
    group.bench_function("method_with_receiver", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(method, "go").unwrap()))
    });

    group.finish();
}

/// Benchmarks for Go struct/interface extraction.
fn bench_go_types(c: &mut Criterion) {
    let mut group = c.benchmark_group("go_types");

    // Struct definition
    let struct_def = go_generators::struct_definition();
    group.throughput(Throughput::Bytes(struct_def.len() as u64));
    group.bench_function("struct_definition", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(struct_def, "go").unwrap()))
    });

    // Interface definition
    let interface_def = go_generators::interface_definition();
    group.throughput(Throughput::Bytes(interface_def.len() as u64));
    group.bench_function("interface_definition", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(interface_def, "go").unwrap()))
    });

    group.finish();
}

/// Benchmarks for Java function extraction.
fn bench_java_functions(c: &mut Criterion) {
    let mut group = c.benchmark_group("java_functions");

    // Annotated method
    let annotated = java_generators::annotated_method();
    group.throughput(Throughput::Bytes(annotated.len() as u64));
    group.bench_function("annotated_method", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(annotated, "java").unwrap()))
    });

    group.finish();
}

/// Benchmarks for Java class extraction.
fn bench_java_classes(c: &mut Criterion) {
    let mut group = c.benchmark_group("java_classes");

    // Generic class with inner classes
    let generic_class = java_generators::generic_class();
    group.throughput(Throughput::Bytes(generic_class.len() as u64));
    group.bench_function("generic_with_inner_classes", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(generic_class, "java").unwrap()))
    });

    group.finish();
}

/// Benchmarks for C function extraction.
fn bench_c_functions(c: &mut Criterion) {
    let mut group = c.benchmark_group("c_functions");

    // Function with macros
    let with_macros = c_generators::function_with_macros();
    group.throughput(Throughput::Bytes(with_macros.len() as u64));
    group.bench_function("with_macros", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(with_macros, "c").unwrap()))
    });

    group.finish();
}

/// Benchmarks for C struct extraction.
fn bench_c_structs(c: &mut Criterion) {
    let mut group = c.benchmark_group("c_structs");

    // Struct with bitfields
    let bitfields = c_generators::struct_with_bitfields();
    group.throughput(Throughput::Bytes(bitfields.len() as u64));
    group.bench_function("with_bitfields", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(bitfields, "c").unwrap()))
    });

    group.finish();
}

/// Benchmarks for C++ class extraction.
fn bench_cpp_classes(c: &mut Criterion) {
    let mut group = c.benchmark_group("cpp_classes");

    // Template class
    let template = cpp_generators::template_class();
    group.throughput(Throughput::Bytes(template.len() as u64));
    group.bench_function("template_class", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(template, "cpp").unwrap()))
    });

    // Class with inheritance
    let inheritance = cpp_generators::class_with_inheritance();
    group.throughput(Throughput::Bytes(inheritance.len() as u64));
    group.bench_function("class_with_inheritance", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(inheritance, "cpp").unwrap()))
    });

    group.finish();
}

/// Benchmarks for scaling behavior with different file sizes.
fn bench_scaling_python(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling_python_functions");

    // Small file (~100 lines)
    let small = python_generators::generate_n_functions(5);
    let small_lines = small.lines().count();
    group.throughput(Throughput::Bytes(small.len() as u64));
    group.bench_with_input(
        BenchmarkId::new("extraction", format!("~{}_lines", small_lines)),
        &small,
        |b, source| {
            b.iter(|| black_box(AstExtractor::extract_from_source(source, "python").unwrap()))
        },
    );

    // Medium file (~500 lines)
    let medium = python_generators::generate_n_functions(25);
    let medium_lines = medium.lines().count();
    group.throughput(Throughput::Bytes(medium.len() as u64));
    group.bench_with_input(
        BenchmarkId::new("extraction", format!("~{}_lines", medium_lines)),
        &medium,
        |b, source| {
            b.iter(|| black_box(AstExtractor::extract_from_source(source, "python").unwrap()))
        },
    );

    // Large file (~1000 lines)
    let large = python_generators::generate_n_functions(50);
    let large_lines = large.lines().count();
    group.throughput(Throughput::Bytes(large.len() as u64));
    group.bench_with_input(
        BenchmarkId::new("extraction", format!("~{}_lines", large_lines)),
        &large,
        |b, source| {
            b.iter(|| black_box(AstExtractor::extract_from_source(source, "python").unwrap()))
        },
    );

    // Very large file (~2000+ lines)
    let very_large = python_generators::generate_n_functions(100);
    let very_large_lines = very_large.lines().count();
    group.throughput(Throughput::Bytes(very_large.len() as u64));
    group.bench_with_input(
        BenchmarkId::new("extraction", format!("~{}_lines", very_large_lines)),
        &very_large,
        |b, source| {
            b.iter(|| black_box(AstExtractor::extract_from_source(source, "python").unwrap()))
        },
    );

    group.finish();
}

/// Benchmarks for scaling with Python classes.
fn bench_scaling_python_classes(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling_python_classes");

    for n_classes in [5, 10, 25, 50] {
        let code = python_generators::generate_n_classes(n_classes);
        let lines = code.lines().count();
        group.throughput(Throughput::Bytes(code.len() as u64));
        group.bench_with_input(
            BenchmarkId::new(
                "extraction",
                format!("{}_classes_~{}_lines", n_classes, lines),
            ),
            &code,
            |b, source| {
                b.iter(|| black_box(AstExtractor::extract_from_source(source, "python").unwrap()))
            },
        );
    }

    group.finish();
}

/// Benchmarks for scaling with TypeScript.
fn bench_scaling_typescript(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling_typescript_functions");

    for n_functions in [5, 25, 50, 100] {
        let code = typescript_generators::generate_n_functions(n_functions);
        let lines = code.lines().count();
        group.throughput(Throughput::Bytes(code.len() as u64));
        group.bench_with_input(
            BenchmarkId::new(
                "extraction",
                format!("{}_functions_~{}_lines", n_functions, lines),
            ),
            &code,
            |b, source| {
                b.iter(|| {
                    black_box(AstExtractor::extract_from_source(source, "typescript").unwrap())
                })
            },
        );
    }

    group.finish();
}

/// Benchmarks for scaling with Rust.
fn bench_scaling_rust(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling_rust_functions");

    for n_functions in [5, 25, 50, 100] {
        let code = rust_generators::generate_n_functions(n_functions);
        let lines = code.lines().count();
        group.throughput(Throughput::Bytes(code.len() as u64));
        group.bench_with_input(
            BenchmarkId::new(
                "extraction",
                format!("{}_functions_~{}_lines", n_functions, lines),
            ),
            &code,
            |b, source| {
                b.iter(|| black_box(AstExtractor::extract_from_source(source, "rust").unwrap()))
            },
        );
    }

    group.finish();
}

/// Benchmarks for scaling with Go.
fn bench_scaling_go(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling_go_functions");

    for n_functions in [5, 25, 50, 100] {
        let code = go_generators::generate_n_functions(n_functions);
        let lines = code.lines().count();
        group.throughput(Throughput::Bytes(code.len() as u64));
        group.bench_with_input(
            BenchmarkId::new(
                "extraction",
                format!("{}_functions_~{}_lines", n_functions, lines),
            ),
            &code,
            |b, source| {
                b.iter(|| black_box(AstExtractor::extract_from_source(source, "go").unwrap()))
            },
        );
    }

    group.finish();
}

/// Benchmarks for scaling with Java.
fn bench_scaling_java(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling_java_methods");

    for n_methods in [5, 25, 50, 100] {
        let code = java_generators::generate_n_methods(n_methods);
        let lines = code.lines().count();
        group.throughput(Throughput::Bytes(code.len() as u64));
        group.bench_with_input(
            BenchmarkId::new(
                "extraction",
                format!("{}_methods_~{}_lines", n_methods, lines),
            ),
            &code,
            |b, source| {
                b.iter(|| black_box(AstExtractor::extract_from_source(source, "java").unwrap()))
            },
        );
    }

    group.finish();
}

/// Benchmarks for parse time vs extraction time breakdown.
fn bench_parse_vs_extraction(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse_vs_extraction");

    // Use Python as representative language
    let code = python_generators::generate_n_functions(25);
    let bytes = code.len() as u64;

    // Parse only
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("python_25_functions_parse_only", |b| {
        let registry = LanguageRegistry::global();
        let lang = registry.get_by_name("python").unwrap();
        b.iter(|| {
            let mut parser = lang.parser().unwrap();
            black_box(parser.parse(code.as_bytes(), None))
        })
    });

    // Full extraction (parse + extract)
    group.throughput(Throughput::Bytes(bytes));
    group.bench_function("python_25_functions_full_extraction", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(&code, "python").unwrap()))
    });

    // Repeat for TypeScript
    let ts_code = typescript_generators::generate_n_functions(25);
    let ts_bytes = ts_code.len() as u64;

    group.throughput(Throughput::Bytes(ts_bytes));
    group.bench_function("typescript_25_functions_parse_only", |b| {
        let registry = LanguageRegistry::global();
        let lang = registry.get_by_name("typescript").unwrap();
        b.iter(|| {
            let mut parser = lang.parser().unwrap();
            black_box(parser.parse(ts_code.as_bytes(), None))
        })
    });

    group.throughput(Throughput::Bytes(ts_bytes));
    group.bench_function("typescript_25_functions_full_extraction", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(&ts_code, "typescript").unwrap()))
    });

    group.finish();
}

/// Benchmarks comparing performance across languages for similar code.
fn bench_cross_language_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("cross_language_50_functions");

    // Python
    let python_code = python_generators::generate_n_functions(50);
    group.throughput(Throughput::Bytes(python_code.len() as u64));
    group.bench_function("python", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(&python_code, "python").unwrap()))
    });

    // TypeScript
    let ts_code = typescript_generators::generate_n_functions(50);
    group.throughput(Throughput::Bytes(ts_code.len() as u64));
    group.bench_function("typescript", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(&ts_code, "typescript").unwrap()))
    });

    // Rust
    let rust_code = rust_generators::generate_n_functions(50);
    group.throughput(Throughput::Bytes(rust_code.len() as u64));
    group.bench_function("rust", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(&rust_code, "rust").unwrap()))
    });

    // Go
    let go_code = go_generators::generate_n_functions(50);
    group.throughput(Throughput::Bytes(go_code.len() as u64));
    group.bench_function("go", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(&go_code, "go").unwrap()))
    });

    // Java
    let java_code = java_generators::generate_n_methods(50);
    group.throughput(Throughput::Bytes(java_code.len() as u64));
    group.bench_function("java", |b| {
        b.iter(|| black_box(AstExtractor::extract_from_source(&java_code, "java").unwrap()))
    });

    group.finish();
}

// =============================================================================
// Criterion Configuration
// =============================================================================

criterion_group!(
    name = python_benches;
    config = Criterion::default().sample_size(100);
    targets = bench_python_functions, bench_python_classes
);

criterion_group!(
    name = typescript_benches;
    config = Criterion::default().sample_size(100);
    targets = bench_typescript_functions, bench_typescript_classes
);

criterion_group!(
    name = rust_benches;
    config = Criterion::default().sample_size(100);
    targets = bench_rust_functions, bench_rust_types
);

criterion_group!(
    name = go_benches;
    config = Criterion::default().sample_size(100);
    targets = bench_go_functions, bench_go_types
);

criterion_group!(
    name = java_benches;
    config = Criterion::default().sample_size(100);
    targets = bench_java_functions, bench_java_classes
);

criterion_group!(
    name = c_benches;
    config = Criterion::default().sample_size(100);
    targets = bench_c_functions, bench_c_structs
);

criterion_group!(
    name = cpp_benches;
    config = Criterion::default().sample_size(100);
    targets = bench_cpp_classes
);

criterion_group!(
    name = scaling_benches;
    config = Criterion::default().sample_size(50);
    targets =
        bench_scaling_python,
        bench_scaling_python_classes,
        bench_scaling_typescript,
        bench_scaling_rust,
        bench_scaling_go,
        bench_scaling_java
);

criterion_group!(
    name = comparison_benches;
    config = Criterion::default().sample_size(50);
    targets = bench_parse_vs_extraction, bench_cross_language_comparison
);

criterion_main!(
    python_benches,
    typescript_benches,
    rust_benches,
    go_benches,
    java_benches,
    c_benches,
    cpp_benches,
    scaling_benches,
    comparison_benches
);
