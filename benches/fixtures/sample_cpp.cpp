/**
 * Sample C++ code for benchmarking AST extraction.
 * Contains modern C++ features including templates, RAII, and smart pointers.
 */

#include <algorithm>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <string>
#include <vector>

namespace benchmark {

/**
 * Generic result type for fallible operations.
 */
template <typename T, typename E = std::string>
class Result {
public:
    static Result ok(T value) { return Result(std::move(value), std::nullopt); }
    static Result err(E error) { return Result(std::nullopt, std::move(error)); }

    bool isOk() const { return value_.has_value(); }
    bool isErr() const { return error_.has_value(); }

    T& value() { return *value_; }
    const T& value() const { return *value_; }

    E& error() { return *error_; }
    const E& error() const { return *error_; }

    T valueOr(T defaultValue) const {
        return isOk() ? *value_ : std::move(defaultValue);
    }

    template <typename F>
    auto map(F&& f) -> Result<decltype(f(std::declval<T>())), E> {
        using U = decltype(f(std::declval<T>()));
        if (isOk()) {
            return Result<U, E>::ok(f(*value_));
        }
        return Result<U, E>::err(*error_);
    }

private:
    Result(std::optional<T> value, std::optional<E> error)
        : value_(std::move(value)), error_(std::move(error)) {}

    std::optional<T> value_;
    std::optional<E> error_;
};

/**
 * 2D Point class.
 */
class Point {
public:
    Point() : x_(0), y_(0) {}
    Point(double x, double y) : x_(x), y_(y) {}

    double x() const { return x_; }
    double y() const { return y_; }

    double distanceTo(const Point& other) const {
        double dx = x_ - other.x_;
        double dy = y_ - other.y_;
        return std::sqrt(dx * dx + dy * dy);
    }

    double magnitude() const { return distanceTo(Point()); }

    Point operator+(const Point& other) const {
        return Point(x_ + other.x_, y_ + other.y_);
    }

    Point operator-(const Point& other) const {
        return Point(x_ - other.x_, y_ - other.y_);
    }

    Point operator*(double scalar) const {
        return Point(x_ * scalar, y_ * scalar);
    }

    bool operator==(const Point& other) const {
        return x_ == other.x_ && y_ == other.y_;
    }

private:
    double x_;
    double y_;
};

/**
 * Rectangle class.
 */
class Rectangle {
public:
    Rectangle(Point topLeft, Point bottomRight)
        : topLeft_(topLeft), bottomRight_(bottomRight) {}

    double width() const { return std::abs(bottomRight_.x() - topLeft_.x()); }
    double height() const { return std::abs(bottomRight_.y() - topLeft_.y()); }
    double area() const { return width() * height(); }
    double perimeter() const { return 2 * (width() + height()); }

    Point center() const {
        return Point(
            (topLeft_.x() + bottomRight_.x()) / 2,
            (topLeft_.y() + bottomRight_.y()) / 2);
    }

    bool contains(const Point& p) const {
        return p.x() >= topLeft_.x() && p.x() <= bottomRight_.x() &&
               p.y() >= topLeft_.y() && p.y() <= bottomRight_.y();
    }

private:
    Point topLeft_;
    Point bottomRight_;
};

/**
 * Generic entity base class.
 */
class Entity {
public:
    Entity(std::string id, std::string name)
        : id_(std::move(id)), name_(std::move(name)),
          createdAt_(std::time(nullptr)), updatedAt_(createdAt_) {}

    virtual ~Entity() = default;

    const std::string& id() const { return id_; }
    const std::string& name() const { return name_; }
    std::time_t createdAt() const { return createdAt_; }
    std::time_t updatedAt() const { return updatedAt_; }

    void setName(const std::string& name) {
        name_ = name;
        touch();
    }

    void setMetadata(const std::string& key, const std::string& value) {
        metadata_[key] = value;
        touch();
    }

    std::optional<std::string> getMetadata(const std::string& key) const {
        auto it = metadata_.find(key);
        if (it != metadata_.end()) {
            return it->second;
        }
        return std::nullopt;
    }

protected:
    void touch() { updatedAt_ = std::time(nullptr); }

private:
    std::string id_;
    std::string name_;
    std::time_t createdAt_;
    std::time_t updatedAt_;
    std::map<std::string, std::string> metadata_;
};

/**
 * User entity.
 */
class User : public Entity {
public:
    enum class Role { Admin, Moderator, User, Guest };

    User(std::string id, std::string username, std::string email)
        : Entity(std::move(id), std::move(username)),
          email_(std::move(email)), role_(Role::User) {}

    const std::string& email() const { return email_; }
    Role role() const { return role_; }

    void setEmail(const std::string& email) {
        email_ = email;
        touch();
    }

    void setRole(Role role) {
        role_ = role;
        touch();
    }

    bool validate() const {
        return !name().empty() && !email_.empty() &&
               email_.find('@') != std::string::npos;
    }

private:
    std::string email_;
    Role role_;
};

/**
 * Generic repository interface.
 */
template <typename T, typename ID = std::string>
class Repository {
public:
    virtual ~Repository() = default;

    virtual std::optional<std::shared_ptr<T>> findById(const ID& id) = 0;
    virtual std::vector<std::shared_ptr<T>> findAll() = 0;
    virtual void save(std::shared_ptr<T> entity) = 0;
    virtual bool remove(const ID& id) = 0;
    virtual size_t count() const = 0;
};

/**
 * In-memory repository implementation.
 */
template <typename T, typename ID = std::string>
class InMemoryRepository : public Repository<T, ID> {
public:
    std::optional<std::shared_ptr<T>> findById(const ID& id) override {
        std::lock_guard<std::mutex> lock(mutex_);
        auto it = storage_.find(id);
        if (it != storage_.end()) {
            return it->second;
        }
        return std::nullopt;
    }

    std::vector<std::shared_ptr<T>> findAll() override {
        std::lock_guard<std::mutex> lock(mutex_);
        std::vector<std::shared_ptr<T>> result;
        result.reserve(storage_.size());
        for (const auto& [_, entity] : storage_) {
            result.push_back(entity);
        }
        return result;
    }

    void save(std::shared_ptr<T> entity) override {
        std::lock_guard<std::mutex> lock(mutex_);
        storage_[entity->id()] = std::move(entity);
    }

    bool remove(const ID& id) override {
        std::lock_guard<std::mutex> lock(mutex_);
        return storage_.erase(id) > 0;
    }

    size_t count() const override {
        std::lock_guard<std::mutex> lock(mutex_);
        return storage_.size();
    }

    void clear() {
        std::lock_guard<std::mutex> lock(mutex_);
        storage_.clear();
    }

private:
    mutable std::mutex mutex_;
    std::map<ID, std::shared_ptr<T>> storage_;
};

/**
 * Simple LRU cache.
 */
template <typename K, typename V>
class LRUCache {
public:
    explicit LRUCache(size_t capacity) : capacity_(capacity) {}

    std::optional<V> get(const K& key) {
        std::lock_guard<std::mutex> lock(mutex_);
        auto it = cache_.find(key);
        if (it == cache_.end()) {
            return std::nullopt;
        }
        touch(key);
        return it->second;
    }

    void put(const K& key, V value) {
        std::lock_guard<std::mutex> lock(mutex_);

        if (cache_.size() >= capacity_ && cache_.find(key) == cache_.end()) {
            evict();
        }

        cache_[key] = std::move(value);
        touch(key);
    }

    bool contains(const K& key) const {
        std::lock_guard<std::mutex> lock(mutex_);
        return cache_.find(key) != cache_.end();
    }

    size_t size() const {
        std::lock_guard<std::mutex> lock(mutex_);
        return cache_.size();
    }

private:
    void touch(const K& key) {
        order_.erase(std::remove(order_.begin(), order_.end(), key), order_.end());
        order_.push_back(key);
    }

    void evict() {
        if (!order_.empty()) {
            K oldest = order_.front();
            order_.erase(order_.begin());
            cache_.erase(oldest);
        }
    }

    size_t capacity_;
    mutable std::mutex mutex_;
    std::map<K, V> cache_;
    std::vector<K> order_;
};

/**
 * Service layer for user management.
 */
class UserService {
public:
    explicit UserService(std::shared_ptr<Repository<User>> repository)
        : repository_(std::move(repository)) {}

    Result<std::shared_ptr<User>> createUser(
        const std::string& username,
        const std::string& email) {

        auto user = std::make_shared<User>(
            generateId(), username, email);

        if (!user->validate()) {
            return Result<std::shared_ptr<User>>::err("Invalid user data");
        }

        repository_->save(user);
        return Result<std::shared_ptr<User>>::ok(user);
    }

    std::optional<std::shared_ptr<User>> findUser(const std::string& id) {
        return repository_->findById(id);
    }

    std::vector<std::shared_ptr<User>> findAllUsers() {
        return repository_->findAll();
    }

    bool deleteUser(const std::string& id) {
        return repository_->remove(id);
    }

private:
    std::string generateId() {
        static int counter = 0;
        return "user_" + std::to_string(++counter);
    }

    std::shared_ptr<Repository<User>> repository_;
};

/**
 * Utility functions.
 */
namespace utils {

template <typename Container, typename Predicate>
auto filter(const Container& c, Predicate pred) {
    Container result;
    std::copy_if(c.begin(), c.end(), std::back_inserter(result), pred);
    return result;
}

template <typename Container, typename Transform>
auto map(const Container& c, Transform f) {
    using ResultType = std::vector<decltype(f(*c.begin()))>;
    ResultType result;
    result.reserve(c.size());
    std::transform(c.begin(), c.end(), std::back_inserter(result), f);
    return result;
}

template <typename Container, typename T>
T reduce(const Container& c, T init, std::function<T(T, typename Container::value_type)> f) {
    return std::accumulate(c.begin(), c.end(), init, f);
}

std::vector<std::string> split(const std::string& s, char delimiter) {
    std::vector<std::string> result;
    std::string token;
    for (char c : s) {
        if (c == delimiter) {
            if (!token.empty()) {
                result.push_back(token);
                token.clear();
            }
        } else {
            token += c;
        }
    }
    if (!token.empty()) {
        result.push_back(token);
    }
    return result;
}

std::string join(const std::vector<std::string>& v, const std::string& delimiter) {
    if (v.empty()) return "";
    std::string result = v[0];
    for (size_t i = 1; i < v.size(); ++i) {
        result += delimiter + v[i];
    }
    return result;
}

} // namespace utils

} // namespace benchmark

int main() {
    using namespace benchmark;

    auto repo = std::make_shared<InMemoryRepository<User>>();
    UserService service(repo);

    auto result = service.createUser("testuser", "test@example.com");
    if (result.isOk()) {
        std::cout << "Created user: " << result.value()->name() << std::endl;
    }

    return 0;
}
