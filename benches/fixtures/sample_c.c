/**
 * Sample C code for benchmarking AST extraction.
 * Contains typical C constructs including structs, functions, and macros.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

/* Constants and macros */
#define MAX_NAME_LENGTH 256
#define MAX_ITEMS 1024
#define INITIAL_CAPACITY 16

#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]))
#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define CLAMP(x, lo, hi) (MIN(MAX(x, lo), hi))

/* Error codes */
typedef enum {
    ERR_SUCCESS = 0,
    ERR_NOMEM = -1,
    ERR_INVALID = -2,
    ERR_NOTFOUND = -3,
    ERR_OVERFLOW = -4
} ErrorCode;

/* Forward declarations */
struct Vector;
struct HashMap;
struct Entity;

/**
 * Result type for operations that can fail.
 */
typedef struct {
    void* value;
    ErrorCode error;
} Result;

/**
 * 2D Point structure.
 */
typedef struct {
    double x;
    double y;
} Point;

/**
 * Create a new point.
 */
Point point_new(double x, double y) {
    Point p = { .x = x, .y = y };
    return p;
}

/**
 * Calculate distance between two points.
 */
double point_distance(const Point* a, const Point* b) {
    double dx = a->x - b->x;
    double dy = a->y - b->y;
    return sqrt(dx * dx + dy * dy);
}

/**
 * Add two points.
 */
Point point_add(const Point* a, const Point* b) {
    return point_new(a->x + b->x, a->y + b->y);
}

/**
 * Scale a point.
 */
Point point_scale(const Point* p, double factor) {
    return point_new(p->x * factor, p->y * factor);
}

/**
 * Rectangle structure.
 */
typedef struct {
    Point top_left;
    Point bottom_right;
} Rectangle;

/**
 * Create a new rectangle.
 */
Rectangle rect_new(Point top_left, Point bottom_right) {
    Rectangle r = { .top_left = top_left, .bottom_right = bottom_right };
    return r;
}

/**
 * Get rectangle width.
 */
double rect_width(const Rectangle* r) {
    return fabs(r->bottom_right.x - r->top_left.x);
}

/**
 * Get rectangle height.
 */
double rect_height(const Rectangle* r) {
    return fabs(r->bottom_right.y - r->top_left.y);
}

/**
 * Get rectangle area.
 */
double rect_area(const Rectangle* r) {
    return rect_width(r) * rect_height(r);
}

/**
 * Check if rectangle contains a point.
 */
bool rect_contains(const Rectangle* r, const Point* p) {
    return p->x >= r->top_left.x && p->x <= r->bottom_right.x &&
           p->y >= r->top_left.y && p->y <= r->bottom_right.y;
}

/**
 * Dynamic array (vector) structure.
 */
typedef struct Vector {
    void** items;
    size_t size;
    size_t capacity;
} Vector;

/**
 * Create a new vector.
 */
Vector* vector_new(void) {
    Vector* v = malloc(sizeof(Vector));
    if (!v) return NULL;

    v->items = malloc(INITIAL_CAPACITY * sizeof(void*));
    if (!v->items) {
        free(v);
        return NULL;
    }

    v->size = 0;
    v->capacity = INITIAL_CAPACITY;
    return v;
}

/**
 * Free a vector.
 */
void vector_free(Vector* v) {
    if (v) {
        free(v->items);
        free(v);
    }
}

/**
 * Resize the vector capacity.
 */
static ErrorCode vector_resize(Vector* v, size_t new_capacity) {
    void** new_items = realloc(v->items, new_capacity * sizeof(void*));
    if (!new_items) return ERR_NOMEM;

    v->items = new_items;
    v->capacity = new_capacity;
    return ERR_SUCCESS;
}

/**
 * Push an item to the vector.
 */
ErrorCode vector_push(Vector* v, void* item) {
    if (!v) return ERR_INVALID;

    if (v->size >= v->capacity) {
        ErrorCode err = vector_resize(v, v->capacity * 2);
        if (err != ERR_SUCCESS) return err;
    }

    v->items[v->size++] = item;
    return ERR_SUCCESS;
}

/**
 * Pop an item from the vector.
 */
void* vector_pop(Vector* v) {
    if (!v || v->size == 0) return NULL;
    return v->items[--v->size];
}

/**
 * Get an item at index.
 */
void* vector_get(const Vector* v, size_t index) {
    if (!v || index >= v->size) return NULL;
    return v->items[index];
}

/**
 * Set an item at index.
 */
ErrorCode vector_set(Vector* v, size_t index, void* item) {
    if (!v || index >= v->size) return ERR_INVALID;
    v->items[index] = item;
    return ERR_SUCCESS;
}

/**
 * Get vector size.
 */
size_t vector_size(const Vector* v) {
    return v ? v->size : 0;
}

/**
 * Check if vector is empty.
 */
bool vector_is_empty(const Vector* v) {
    return vector_size(v) == 0;
}

/**
 * Hash map entry.
 */
typedef struct HashEntry {
    char* key;
    void* value;
    struct HashEntry* next;
} HashEntry;

/**
 * Hash map structure.
 */
typedef struct HashMap {
    HashEntry** buckets;
    size_t bucket_count;
    size_t size;
} HashMap;

/**
 * Simple string hash function.
 */
static size_t hash_string(const char* key, size_t bucket_count) {
    size_t hash = 5381;
    int c;
    while ((c = *key++)) {
        hash = ((hash << 5) + hash) + c;
    }
    return hash % bucket_count;
}

/**
 * Create a new hash map.
 */
HashMap* hashmap_new(size_t bucket_count) {
    HashMap* map = malloc(sizeof(HashMap));
    if (!map) return NULL;

    map->buckets = calloc(bucket_count, sizeof(HashEntry*));
    if (!map->buckets) {
        free(map);
        return NULL;
    }

    map->bucket_count = bucket_count;
    map->size = 0;
    return map;
}

/**
 * Free a hash map.
 */
void hashmap_free(HashMap* map) {
    if (!map) return;

    for (size_t i = 0; i < map->bucket_count; i++) {
        HashEntry* entry = map->buckets[i];
        while (entry) {
            HashEntry* next = entry->next;
            free(entry->key);
            free(entry);
            entry = next;
        }
    }

    free(map->buckets);
    free(map);
}

/**
 * Put a key-value pair in the map.
 */
ErrorCode hashmap_put(HashMap* map, const char* key, void* value) {
    if (!map || !key) return ERR_INVALID;

    size_t index = hash_string(key, map->bucket_count);

    /* Check for existing key */
    HashEntry* entry = map->buckets[index];
    while (entry) {
        if (strcmp(entry->key, key) == 0) {
            entry->value = value;
            return ERR_SUCCESS;
        }
        entry = entry->next;
    }

    /* Create new entry */
    HashEntry* new_entry = malloc(sizeof(HashEntry));
    if (!new_entry) return ERR_NOMEM;

    new_entry->key = strdup(key);
    if (!new_entry->key) {
        free(new_entry);
        return ERR_NOMEM;
    }

    new_entry->value = value;
    new_entry->next = map->buckets[index];
    map->buckets[index] = new_entry;
    map->size++;

    return ERR_SUCCESS;
}

/**
 * Get a value from the map.
 */
void* hashmap_get(const HashMap* map, const char* key) {
    if (!map || !key) return NULL;

    size_t index = hash_string(key, map->bucket_count);
    HashEntry* entry = map->buckets[index];

    while (entry) {
        if (strcmp(entry->key, key) == 0) {
            return entry->value;
        }
        entry = entry->next;
    }

    return NULL;
}

/**
 * Remove a key from the map.
 */
void* hashmap_remove(HashMap* map, const char* key) {
    if (!map || !key) return NULL;

    size_t index = hash_string(key, map->bucket_count);
    HashEntry* entry = map->buckets[index];
    HashEntry* prev = NULL;

    while (entry) {
        if (strcmp(entry->key, key) == 0) {
            if (prev) {
                prev->next = entry->next;
            } else {
                map->buckets[index] = entry->next;
            }

            void* value = entry->value;
            free(entry->key);
            free(entry);
            map->size--;
            return value;
        }
        prev = entry;
        entry = entry->next;
    }

    return NULL;
}

/**
 * Check if map contains a key.
 */
bool hashmap_contains(const HashMap* map, const char* key) {
    return hashmap_get(map, key) != NULL;
}

/**
 * Get map size.
 */
size_t hashmap_size(const HashMap* map) {
    return map ? map->size : 0;
}

/**
 * Entity structure representing a generic entity.
 */
typedef struct Entity {
    char id[37];  /* UUID format */
    char name[MAX_NAME_LENGTH];
    int64_t created_at;
    int64_t updated_at;
    HashMap* metadata;
} Entity;

/**
 * Create a new entity.
 */
Entity* entity_new(const char* id, const char* name) {
    Entity* e = malloc(sizeof(Entity));
    if (!e) return NULL;

    strncpy(e->id, id, sizeof(e->id) - 1);
    e->id[sizeof(e->id) - 1] = '\0';

    strncpy(e->name, name, sizeof(e->name) - 1);
    e->name[sizeof(e->name) - 1] = '\0';

    e->created_at = time(NULL);
    e->updated_at = e->created_at;
    e->metadata = hashmap_new(16);

    return e;
}

/**
 * Free an entity.
 */
void entity_free(Entity* e) {
    if (e) {
        hashmap_free(e->metadata);
        free(e);
    }
}

/**
 * Set entity metadata.
 */
ErrorCode entity_set_metadata(Entity* e, const char* key, void* value) {
    if (!e) return ERR_INVALID;
    e->updated_at = time(NULL);
    return hashmap_put(e->metadata, key, value);
}

/**
 * Get entity metadata.
 */
void* entity_get_metadata(const Entity* e, const char* key) {
    if (!e) return NULL;
    return hashmap_get(e->metadata, key);
}

/* Main function for testing */
int main(int argc, char** argv) {
    /* Test vector */
    Vector* v = vector_new();
    int values[] = {1, 2, 3, 4, 5};

    for (size_t i = 0; i < ARRAY_SIZE(values); i++) {
        vector_push(v, &values[i]);
    }

    printf("Vector size: %zu\n", vector_size(v));
    vector_free(v);

    /* Test hashmap */
    HashMap* map = hashmap_new(16);
    hashmap_put(map, "key1", "value1");
    hashmap_put(map, "key2", "value2");

    printf("Map size: %zu\n", hashmap_size(map));
    printf("key1 = %s\n", (char*)hashmap_get(map, "key1"));

    hashmap_free(map);

    return 0;
}
