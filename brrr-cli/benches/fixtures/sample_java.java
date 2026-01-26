package com.example.benchmark;

import java.util.*;
import java.util.concurrent.*;
import java.util.function.*;
import java.util.stream.*;

/**
 * Sample Java code for benchmarking AST extraction.
 * Contains classes, interfaces, generics, and annotations.
 */
public class SampleBenchmark {

    /**
     * Generic interface for repository pattern.
     * @param <T> Entity type
     * @param <ID> ID type
     */
    public interface Repository<T, ID> {
        Optional<T> findById(ID id);
        List<T> findAll();
        T save(T entity);
        void delete(ID id);
        boolean existsById(ID id);
    }

    /**
     * Base entity class with common fields.
     */
    public static abstract class BaseEntity {
        private String id;
        private long createdAt;
        private long updatedAt;

        public BaseEntity() {
            this.id = UUID.randomUUID().toString();
            this.createdAt = System.currentTimeMillis();
            this.updatedAt = this.createdAt;
        }

        public String getId() {
            return id;
        }

        public void setId(String id) {
            this.id = id;
        }

        public long getCreatedAt() {
            return createdAt;
        }

        public long getUpdatedAt() {
            return updatedAt;
        }

        protected void touch() {
            this.updatedAt = System.currentTimeMillis();
        }
    }

    /**
     * User entity representing a system user.
     */
    public static class User extends BaseEntity {
        private String username;
        private String email;
        private UserRole role;
        private Map<String, String> metadata;

        public User(String username, String email) {
            super();
            this.username = username;
            this.email = email;
            this.role = UserRole.USER;
            this.metadata = new HashMap<>();
        }

        public String getUsername() {
            return username;
        }

        public void setUsername(String username) {
            this.username = username;
            touch();
        }

        public String getEmail() {
            return email;
        }

        public void setEmail(String email) {
            this.email = email;
            touch();
        }

        public UserRole getRole() {
            return role;
        }

        public void setRole(UserRole role) {
            this.role = role;
            touch();
        }

        public void setMetadata(String key, String value) {
            this.metadata.put(key, value);
        }

        public Optional<String> getMetadata(String key) {
            return Optional.ofNullable(metadata.get(key));
        }

        public boolean validate() {
            return username != null && !username.isEmpty()
                && email != null && email.contains("@");
        }
    }

    /**
     * User role enumeration.
     */
    public enum UserRole {
        ADMIN("admin", 100),
        MODERATOR("moderator", 50),
        USER("user", 10),
        GUEST("guest", 1);

        private final String name;
        private final int level;

        UserRole(String name, int level) {
            this.name = name;
            this.level = level;
        }

        public String getName() {
            return name;
        }

        public int getLevel() {
            return level;
        }

        public boolean hasPermission(int requiredLevel) {
            return this.level >= requiredLevel;
        }
    }

    /**
     * In-memory repository implementation.
     * @param <T> Entity type extending BaseEntity
     */
    public static class InMemoryRepository<T extends BaseEntity>
            implements Repository<T, String> {

        private final Map<String, T> storage = new ConcurrentHashMap<>();

        @Override
        public Optional<T> findById(String id) {
            return Optional.ofNullable(storage.get(id));
        }

        @Override
        public List<T> findAll() {
            return new ArrayList<>(storage.values());
        }

        @Override
        public T save(T entity) {
            storage.put(entity.getId(), entity);
            return entity;
        }

        @Override
        public void delete(String id) {
            storage.remove(id);
        }

        @Override
        public boolean existsById(String id) {
            return storage.containsKey(id);
        }

        public int count() {
            return storage.size();
        }

        public void clear() {
            storage.clear();
        }
    }

    /**
     * Service layer for user management.
     */
    public static class UserService {
        private final Repository<User, String> repository;
        private final ExecutorService executor;

        public UserService(Repository<User, String> repository) {
            this.repository = repository;
            this.executor = Executors.newFixedThreadPool(4);
        }

        public User createUser(String username, String email) {
            User user = new User(username, email);
            if (!user.validate()) {
                throw new IllegalArgumentException("Invalid user data");
            }
            return repository.save(user);
        }

        public Optional<User> findUser(String id) {
            return repository.findById(id);
        }

        public List<User> findAllUsers() {
            return repository.findAll();
        }

        public CompletableFuture<User> createUserAsync(String username, String email) {
            return CompletableFuture.supplyAsync(
                () -> createUser(username, email),
                executor
            );
        }

        public void shutdown() {
            executor.shutdown();
        }
    }

    /**
     * Generic result type for operations.
     * @param <T> Success value type
     * @param <E> Error type
     */
    public static class Result<T, E> {
        private final T value;
        private final E error;
        private final boolean success;

        private Result(T value, E error, boolean success) {
            this.value = value;
            this.error = error;
            this.success = success;
        }

        public static <T, E> Result<T, E> ok(T value) {
            return new Result<>(value, null, true);
        }

        public static <T, E> Result<T, E> err(E error) {
            return new Result<>(null, error, false);
        }

        public boolean isSuccess() {
            return success;
        }

        public boolean isError() {
            return !success;
        }

        public T getValue() {
            if (!success) {
                throw new IllegalStateException("No value present");
            }
            return value;
        }

        public E getError() {
            if (success) {
                throw new IllegalStateException("No error present");
            }
            return error;
        }

        public <U> Result<U, E> map(Function<T, U> mapper) {
            if (success) {
                return Result.ok(mapper.apply(value));
            }
            return Result.err(error);
        }

        public <F> Result<T, F> mapError(Function<E, F> mapper) {
            if (!success) {
                return Result.err(mapper.apply(error));
            }
            return Result.ok(value);
        }

        public T orElse(T defaultValue) {
            return success ? value : defaultValue;
        }

        public T orElseGet(Supplier<T> supplier) {
            return success ? value : supplier.get();
        }
    }

    /**
     * Simple LRU cache implementation.
     * @param <K> Key type
     * @param <V> Value type
     */
    public static class LRUCache<K, V> extends LinkedHashMap<K, V> {
        private final int capacity;

        public LRUCache(int capacity) {
            super(capacity, 0.75f, true);
            this.capacity = capacity;
        }

        @Override
        protected boolean removeEldestEntry(Map.Entry<K, V> eldest) {
            return size() > capacity;
        }

        public synchronized V getOrCompute(K key, Function<K, V> computer) {
            return computeIfAbsent(key, computer);
        }
    }

    /**
     * Builder pattern implementation for configuration.
     */
    public static class ConfigBuilder {
        private String host = "localhost";
        private int port = 8080;
        private int timeout = 30000;
        private boolean ssl = false;
        private Map<String, String> headers = new HashMap<>();

        public ConfigBuilder host(String host) {
            this.host = host;
            return this;
        }

        public ConfigBuilder port(int port) {
            this.port = port;
            return this;
        }

        public ConfigBuilder timeout(int timeout) {
            this.timeout = timeout;
            return this;
        }

        public ConfigBuilder ssl(boolean ssl) {
            this.ssl = ssl;
            return this;
        }

        public ConfigBuilder header(String key, String value) {
            this.headers.put(key, value);
            return this;
        }

        public Config build() {
            return new Config(host, port, timeout, ssl, headers);
        }
    }

    /**
     * Immutable configuration class.
     */
    public static class Config {
        private final String host;
        private final int port;
        private final int timeout;
        private final boolean ssl;
        private final Map<String, String> headers;

        Config(String host, int port, int timeout, boolean ssl,
               Map<String, String> headers) {
            this.host = host;
            this.port = port;
            this.timeout = timeout;
            this.ssl = ssl;
            this.headers = Collections.unmodifiableMap(new HashMap<>(headers));
        }

        public String getHost() { return host; }
        public int getPort() { return port; }
        public int getTimeout() { return timeout; }
        public boolean isSsl() { return ssl; }
        public Map<String, String> getHeaders() { return headers; }

        public String getUrl() {
            String protocol = ssl ? "https" : "http";
            return String.format("%s://%s:%d", protocol, host, port);
        }
    }

    /**
     * Utility class with static helper methods.
     */
    public static final class Utils {
        private Utils() {}

        public static <T> List<T> filter(List<T> list, Predicate<T> predicate) {
            return list.stream()
                .filter(predicate)
                .collect(Collectors.toList());
        }

        public static <T, R> List<R> map(List<T> list, Function<T, R> mapper) {
            return list.stream()
                .map(mapper)
                .collect(Collectors.toList());
        }

        public static <T> Optional<T> find(List<T> list, Predicate<T> predicate) {
            return list.stream()
                .filter(predicate)
                .findFirst();
        }

        public static <T, K> Map<K, List<T>> groupBy(List<T> list,
                Function<T, K> classifier) {
            return list.stream()
                .collect(Collectors.groupingBy(classifier));
        }

        public static String join(List<String> strings, String delimiter) {
            return String.join(delimiter, strings);
        }

        public static <T> T retry(Supplier<T> supplier, int maxAttempts,
                long delayMs) throws InterruptedException {
            Exception lastException = null;
            for (int i = 0; i < maxAttempts; i++) {
                try {
                    return supplier.get();
                } catch (Exception e) {
                    lastException = e;
                    if (i < maxAttempts - 1) {
                        Thread.sleep(delayMs);
                    }
                }
            }
            throw new RuntimeException("All retry attempts failed", lastException);
        }
    }

    public static void main(String[] args) {
        InMemoryRepository<User> repo = new InMemoryRepository<>();
        UserService service = new UserService(repo);

        User user = service.createUser("test", "test@example.com");
        System.out.println("Created user: " + user.getUsername());

        service.shutdown();
    }
}
