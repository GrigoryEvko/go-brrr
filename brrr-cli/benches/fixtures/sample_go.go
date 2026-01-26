// Package sample provides sample Go code for benchmarking AST extraction.
package sample

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"sync"
	"time"
)

// Error types for the package.
var (
	ErrNotFound    = errors.New("item not found")
	ErrInvalidData = errors.New("invalid data")
	ErrTimeout     = errors.New("operation timed out")
)

// Entity represents a generic entity with common fields.
type Entity struct {
	ID        string            `json:"id"`
	CreatedAt time.Time         `json:"created_at"`
	UpdatedAt time.Time         `json:"updated_at"`
	Metadata  map[string]string `json:"metadata,omitempty"`
}

// NewEntity creates a new entity with the given ID.
func NewEntity(id string) *Entity {
	now := time.Now()
	return &Entity{
		ID:        id,
		CreatedAt: now,
		UpdatedAt: now,
		Metadata:  make(map[string]string),
	}
}

// SetMetadata sets a metadata key-value pair.
func (e *Entity) SetMetadata(key, value string) {
	e.Metadata[key] = value
	e.UpdatedAt = time.Now()
}

// GetMetadata retrieves a metadata value by key.
func (e *Entity) GetMetadata(key string) (string, bool) {
	value, ok := e.Metadata[key]
	return value, ok
}

// User represents a user in the system.
type User struct {
	Entity
	Username string `json:"username"`
	Email    string `json:"email"`
	Role     string `json:"role"`
}

// NewUser creates a new user.
func NewUser(id, username, email string) *User {
	return &User{
		Entity:   *NewEntity(id),
		Username: username,
		Email:    email,
		Role:     "user",
	}
}

// Validate validates the user data.
func (u *User) Validate() error {
	if u.Username == "" {
		return errors.New("username is required")
	}
	if u.Email == "" {
		return errors.New("email is required")
	}
	return nil
}

// Repository defines the interface for data access.
type Repository[T any] interface {
	FindByID(ctx context.Context, id string) (*T, error)
	FindAll(ctx context.Context) ([]*T, error)
	Create(ctx context.Context, item *T) error
	Update(ctx context.Context, item *T) error
	Delete(ctx context.Context, id string) error
}

// InMemoryRepository is an in-memory implementation of Repository.
type InMemoryRepository[T any] struct {
	mu    sync.RWMutex
	items map[string]*T
	getID func(*T) string
}

// NewInMemoryRepository creates a new in-memory repository.
func NewInMemoryRepository[T any](getID func(*T) string) *InMemoryRepository[T] {
	return &InMemoryRepository[T]{
		items: make(map[string]*T),
		getID: getID,
	}
}

// FindByID finds an item by ID.
func (r *InMemoryRepository[T]) FindByID(ctx context.Context, id string) (*T, error) {
	r.mu.RLock()
	defer r.mu.RUnlock()

	if item, ok := r.items[id]; ok {
		return item, nil
	}
	return nil, ErrNotFound
}

// FindAll returns all items.
func (r *InMemoryRepository[T]) FindAll(ctx context.Context) ([]*T, error) {
	r.mu.RLock()
	defer r.mu.RUnlock()

	result := make([]*T, 0, len(r.items))
	for _, item := range r.items {
		result = append(result, item)
	}
	return result, nil
}

// Create adds a new item.
func (r *InMemoryRepository[T]) Create(ctx context.Context, item *T) error {
	r.mu.Lock()
	defer r.mu.Unlock()

	id := r.getID(item)
	if _, exists := r.items[id]; exists {
		return errors.New("item already exists")
	}
	r.items[id] = item
	return nil
}

// Update updates an existing item.
func (r *InMemoryRepository[T]) Update(ctx context.Context, item *T) error {
	r.mu.Lock()
	defer r.mu.Unlock()

	id := r.getID(item)
	if _, exists := r.items[id]; !exists {
		return ErrNotFound
	}
	r.items[id] = item
	return nil
}

// Delete removes an item.
func (r *InMemoryRepository[T]) Delete(ctx context.Context, id string) error {
	r.mu.Lock()
	defer r.mu.Unlock()

	if _, exists := r.items[id]; !exists {
		return ErrNotFound
	}
	delete(r.items, id)
	return nil
}

// Cache is a simple thread-safe cache.
type Cache[K comparable, V any] struct {
	mu       sync.RWMutex
	items    map[K]cacheItem[V]
	capacity int
	ttl      time.Duration
}

type cacheItem[V any] struct {
	value     V
	expiresAt time.Time
}

// NewCache creates a new cache.
func NewCache[K comparable, V any](capacity int, ttl time.Duration) *Cache[K, V] {
	return &Cache[K, V]{
		items:    make(map[K]cacheItem[V]),
		capacity: capacity,
		ttl:      ttl,
	}
}

// Get retrieves a value from the cache.
func (c *Cache[K, V]) Get(key K) (V, bool) {
	c.mu.RLock()
	defer c.mu.RUnlock()

	item, ok := c.items[key]
	if !ok || time.Now().After(item.expiresAt) {
		var zero V
		return zero, false
	}
	return item.value, true
}

// Set stores a value in the cache.
func (c *Cache[K, V]) Set(key K, value V) {
	c.mu.Lock()
	defer c.mu.Unlock()

	if len(c.items) >= c.capacity {
		c.evictExpired()
	}

	c.items[key] = cacheItem[V]{
		value:     value,
		expiresAt: time.Now().Add(c.ttl),
	}
}

// Delete removes a value from the cache.
func (c *Cache[K, V]) Delete(key K) {
	c.mu.Lock()
	defer c.mu.Unlock()
	delete(c.items, key)
}

func (c *Cache[K, V]) evictExpired() {
	now := time.Now()
	for key, item := range c.items {
		if now.After(item.expiresAt) {
			delete(c.items, key)
		}
	}
}

// Worker processes tasks asynchronously.
type Worker struct {
	id       int
	tasks    chan func()
	quit     chan struct{}
	wg       *sync.WaitGroup
}

// NewWorker creates a new worker.
func NewWorker(id int, tasks chan func(), wg *sync.WaitGroup) *Worker {
	return &Worker{
		id:    id,
		tasks: tasks,
		quit:  make(chan struct{}),
		wg:    wg,
	}
}

// Start begins processing tasks.
func (w *Worker) Start() {
	go func() {
		for {
			select {
			case task := <-w.tasks:
				task()
				w.wg.Done()
			case <-w.quit:
				return
			}
		}
	}()
}

// Stop signals the worker to stop.
func (w *Worker) Stop() {
	close(w.quit)
}

// WorkerPool manages a pool of workers.
type WorkerPool struct {
	workers []*Worker
	tasks   chan func()
	wg      sync.WaitGroup
}

// NewWorkerPool creates a new worker pool.
func NewWorkerPool(size int) *WorkerPool {
	pool := &WorkerPool{
		workers: make([]*Worker, size),
		tasks:   make(chan func(), 100),
	}

	for i := 0; i < size; i++ {
		pool.workers[i] = NewWorker(i, pool.tasks, &pool.wg)
		pool.workers[i].Start()
	}

	return pool
}

// Submit submits a task to the pool.
func (p *WorkerPool) Submit(task func()) {
	p.wg.Add(1)
	p.tasks <- task
}

// Wait waits for all tasks to complete.
func (p *WorkerPool) Wait() {
	p.wg.Wait()
}

// Shutdown stops all workers.
func (p *WorkerPool) Shutdown() {
	for _, worker := range p.workers {
		worker.Stop()
	}
}

// Result represents the result of an operation.
type Result[T any] struct {
	Value T
	Error error
}

// OK creates a successful result.
func OK[T any](value T) Result[T] {
	return Result[T]{Value: value}
}

// Err creates an error result.
func Err[T any](err error) Result[T] {
	return Result[T]{Error: err}
}

// IsOK returns true if the result is successful.
func (r Result[T]) IsOK() bool {
	return r.Error == nil
}

// Unwrap returns the value or panics if there's an error.
func (r Result[T]) Unwrap() T {
	if r.Error != nil {
		panic(r.Error)
	}
	return r.Value
}

// UnwrapOr returns the value or a default.
func (r Result[T]) UnwrapOr(defaultValue T) T {
	if r.Error != nil {
		return defaultValue
	}
	return r.Value
}
