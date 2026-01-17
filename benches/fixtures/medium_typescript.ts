/**
 * Medium-sized TypeScript module for benchmarking AST extraction.
 * Contains classes, interfaces, generics, decorators, and async patterns.
 */

import { EventEmitter } from 'events';

// Type definitions and interfaces
export interface Entity {
    id: string;
    createdAt: Date;
    updatedAt: Date;
}

export interface User extends Entity {
    username: string;
    email: string;
    role: UserRole;
    profile?: UserProfile;
}

export interface UserProfile {
    firstName: string;
    lastName: string;
    avatar?: string;
    bio?: string;
    preferences: UserPreferences;
}

export interface UserPreferences {
    theme: 'light' | 'dark' | 'system';
    notifications: boolean;
    language: string;
}

export enum UserRole {
    Admin = 'admin',
    Moderator = 'moderator',
    User = 'user',
    Guest = 'guest',
}

export type Nullable<T> = T | null;
export type Optional<T> = T | undefined;
export type Result<T, E = Error> = { success: true; data: T } | { success: false; error: E };

// Decorator functions
function log(target: any, propertyKey: string, descriptor: PropertyDescriptor): PropertyDescriptor {
    const originalMethod = descriptor.value;
    descriptor.value = function (...args: any[]) {
        console.log(`Calling ${propertyKey} with args:`, args);
        const result = originalMethod.apply(this, args);
        console.log(`${propertyKey} returned:`, result);
        return result;
    };
    return descriptor;
}

function memoize(target: any, propertyKey: string, descriptor: PropertyDescriptor): PropertyDescriptor {
    const originalMethod = descriptor.value;
    const cache = new Map<string, any>();
    descriptor.value = function (...args: any[]) {
        const key = JSON.stringify(args);
        if (cache.has(key)) {
            return cache.get(key);
        }
        const result = originalMethod.apply(this, args);
        cache.set(key, result);
        return result;
    };
    return descriptor;
}

function validate(schema: Record<string, string>): MethodDecorator {
    return function (target: any, propertyKey: string | symbol, descriptor: PropertyDescriptor) {
        const originalMethod = descriptor.value;
        descriptor.value = function (data: Record<string, any>) {
            for (const [key, type] of Object.entries(schema)) {
                if (typeof data[key] !== type) {
                    throw new Error(`Invalid type for ${key}: expected ${type}`);
                }
            }
            return originalMethod.apply(this, [data]);
        };
        return descriptor;
    };
}

// Generic classes and interfaces
export interface Repository<T extends Entity> {
    findById(id: string): Promise<Nullable<T>>;
    findAll(filter?: Partial<T>): Promise<T[]>;
    create(entity: Omit<T, 'id' | 'createdAt' | 'updatedAt'>): Promise<T>;
    update(id: string, entity: Partial<T>): Promise<Nullable<T>>;
    delete(id: string): Promise<boolean>;
}

export abstract class BaseRepository<T extends Entity> implements Repository<T> {
    protected entities: Map<string, T> = new Map();
    protected eventEmitter: EventEmitter = new EventEmitter();

    abstract generateId(): string;

    async findById(id: string): Promise<Nullable<T>> {
        return this.entities.get(id) ?? null;
    }

    async findAll(filter?: Partial<T>): Promise<T[]> {
        const all = Array.from(this.entities.values());
        if (!filter) return all;
        return all.filter(entity => {
            for (const [key, value] of Object.entries(filter)) {
                if (entity[key as keyof T] !== value) return false;
            }
            return true;
        });
    }

    async create(data: Omit<T, 'id' | 'createdAt' | 'updatedAt'>): Promise<T> {
        const now = new Date();
        const entity = {
            ...data,
            id: this.generateId(),
            createdAt: now,
            updatedAt: now,
        } as T;
        this.entities.set(entity.id, entity);
        this.eventEmitter.emit('created', entity);
        return entity;
    }

    async update(id: string, data: Partial<T>): Promise<Nullable<T>> {
        const existing = this.entities.get(id);
        if (!existing) return null;
        const updated = {
            ...existing,
            ...data,
            id: existing.id,
            createdAt: existing.createdAt,
            updatedAt: new Date(),
        };
        this.entities.set(id, updated);
        this.eventEmitter.emit('updated', updated);
        return updated;
    }

    async delete(id: string): Promise<boolean> {
        const existed = this.entities.has(id);
        if (existed) {
            const entity = this.entities.get(id);
            this.entities.delete(id);
            this.eventEmitter.emit('deleted', entity);
        }
        return existed;
    }

    on(event: 'created' | 'updated' | 'deleted', handler: (entity: T) => void): void {
        this.eventEmitter.on(event, handler);
    }
}

// Concrete repository implementation
export class UserRepository extends BaseRepository<User> {
    private counter: number = 0;

    generateId(): string {
        return `user_${++this.counter}_${Date.now()}`;
    }

    async findByEmail(email: string): Promise<Nullable<User>> {
        const all = await this.findAll();
        return all.find(u => u.email === email) ?? null;
    }

    async findByUsername(username: string): Promise<Nullable<User>> {
        const all = await this.findAll();
        return all.find(u => u.username === username) ?? null;
    }

    async findByRole(role: UserRole): Promise<User[]> {
        return this.findAll({ role });
    }
}

// Service layer
export class UserService {
    constructor(private readonly repository: UserRepository) {}

    @log
    async createUser(
        username: string,
        email: string,
        role: UserRole = UserRole.User,
    ): Promise<Result<User>> {
        try {
            const existingEmail = await this.repository.findByEmail(email);
            if (existingEmail) {
                return { success: false, error: new Error('Email already exists') };
            }

            const existingUsername = await this.repository.findByUsername(username);
            if (existingUsername) {
                return { success: false, error: new Error('Username already exists') };
            }

            const user = await this.repository.create({ username, email, role });
            return { success: true, data: user };
        } catch (error) {
            return { success: false, error: error as Error };
        }
    }

    @memoize
    async getUserById(id: string): Promise<Nullable<User>> {
        return this.repository.findById(id);
    }

    async updateUserProfile(id: string, profile: Partial<UserProfile>): Promise<Result<User>> {
        try {
            const user = await this.repository.findById(id);
            if (!user) {
                return { success: false, error: new Error('User not found') };
            }

            const updated = await this.repository.update(id, {
                profile: { ...user.profile, ...profile } as UserProfile,
            });

            if (!updated) {
                return { success: false, error: new Error('Failed to update') };
            }

            return { success: true, data: updated };
        } catch (error) {
            return { success: false, error: error as Error };
        }
    }

    async deleteUser(id: string): Promise<boolean> {
        return this.repository.delete(id);
    }
}

// Utility functions
export function generateUUID(): string {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, c => {
        const r = (Math.random() * 16) | 0;
        const v = c === 'x' ? r : (r & 0x3) | 0x8;
        return v.toString(16);
    });
}

export function debounce<T extends (...args: any[]) => any>(
    fn: T,
    delay: number,
): (...args: Parameters<T>) => void {
    let timeoutId: ReturnType<typeof setTimeout>;
    return (...args: Parameters<T>) => {
        clearTimeout(timeoutId);
        timeoutId = setTimeout(() => fn(...args), delay);
    };
}

export function throttle<T extends (...args: any[]) => any>(
    fn: T,
    limit: number,
): (...args: Parameters<T>) => void {
    let inThrottle = false;
    return (...args: Parameters<T>) => {
        if (!inThrottle) {
            fn(...args);
            inThrottle = true;
            setTimeout(() => (inThrottle = false), limit);
        }
    };
}

export function deepClone<T>(obj: T): T {
    if (obj === null || typeof obj !== 'object') return obj;
    if (obj instanceof Date) return new Date(obj.getTime()) as unknown as T;
    if (obj instanceof Array) return obj.map(item => deepClone(item)) as unknown as T;
    if (obj instanceof Object) {
        const cloned = {} as T;
        for (const key in obj) {
            if (Object.prototype.hasOwnProperty.call(obj, key)) {
                cloned[key] = deepClone(obj[key]);
            }
        }
        return cloned;
    }
    return obj;
}

export function pick<T extends object, K extends keyof T>(obj: T, keys: K[]): Pick<T, K> {
    const result = {} as Pick<T, K>;
    for (const key of keys) {
        if (key in obj) {
            result[key] = obj[key];
        }
    }
    return result;
}

export function omit<T extends object, K extends keyof T>(obj: T, keys: K[]): Omit<T, K> {
    const result = { ...obj };
    for (const key of keys) {
        delete result[key];
    }
    return result;
}

// Async utilities
export async function retry<T>(
    fn: () => Promise<T>,
    maxAttempts: number = 3,
    delay: number = 1000,
): Promise<T> {
    let lastError: Error | undefined;
    for (let attempt = 1; attempt <= maxAttempts; attempt++) {
        try {
            return await fn();
        } catch (error) {
            lastError = error as Error;
            if (attempt < maxAttempts) {
                await new Promise(resolve => setTimeout(resolve, delay * attempt));
            }
        }
    }
    throw lastError;
}

export async function timeout<T>(promise: Promise<T>, ms: number): Promise<T> {
    const timeoutPromise = new Promise<never>((_, reject) => {
        setTimeout(() => reject(new Error('Operation timed out')), ms);
    });
    return Promise.race([promise, timeoutPromise]);
}

export async function parallel<T>(
    tasks: (() => Promise<T>)[],
    concurrency: number = 5,
): Promise<T[]> {
    const results: T[] = [];
    const executing: Promise<void>[] = [];

    for (const task of tasks) {
        const p = task().then(result => {
            results.push(result);
        });

        executing.push(p);

        if (executing.length >= concurrency) {
            await Promise.race(executing);
            executing.splice(
                executing.findIndex(e => e === p),
                1,
            );
        }
    }

    await Promise.all(executing);
    return results;
}

// Event handling
export class TypedEventEmitter<T extends Record<string, any[]>> {
    private handlers: Map<keyof T, Set<(...args: any[]) => void>> = new Map();

    on<K extends keyof T>(event: K, handler: (...args: T[K]) => void): () => void {
        if (!this.handlers.has(event)) {
            this.handlers.set(event, new Set());
        }
        this.handlers.get(event)!.add(handler);
        return () => this.off(event, handler);
    }

    off<K extends keyof T>(event: K, handler: (...args: T[K]) => void): void {
        this.handlers.get(event)?.delete(handler);
    }

    emit<K extends keyof T>(event: K, ...args: T[K]): void {
        this.handlers.get(event)?.forEach(handler => handler(...args));
    }

    once<K extends keyof T>(event: K, handler: (...args: T[K]) => void): () => void {
        const wrapper = (...args: T[K]) => {
            handler(...args);
            this.off(event, wrapper);
        };
        return this.on(event, wrapper);
    }
}

// State management
export class Store<S> {
    private state: S;
    private listeners: Set<(state: S) => void> = new Set();

    constructor(initialState: S) {
        this.state = initialState;
    }

    getState(): S {
        return this.state;
    }

    setState(updater: Partial<S> | ((prev: S) => Partial<S>)): void {
        const update = typeof updater === 'function' ? updater(this.state) : updater;
        this.state = { ...this.state, ...update };
        this.notify();
    }

    subscribe(listener: (state: S) => void): () => void {
        this.listeners.add(listener);
        return () => this.listeners.delete(listener);
    }

    private notify(): void {
        this.listeners.forEach(listener => listener(this.state));
    }
}

// Validation utilities
export interface ValidationRule<T> {
    validate(value: T): boolean;
    message: string;
}

export class Validator<T> {
    private rules: ValidationRule<T>[] = [];

    addRule(rule: ValidationRule<T>): this {
        this.rules.push(rule);
        return this;
    }

    required(): this {
        return this.addRule({
            validate: value => value !== null && value !== undefined,
            message: 'Value is required',
        });
    }

    validate(value: T): { valid: boolean; errors: string[] } {
        const errors: string[] = [];
        for (const rule of this.rules) {
            if (!rule.validate(value)) {
                errors.push(rule.message);
            }
        }
        return { valid: errors.length === 0, errors };
    }
}

export class StringValidator extends Validator<string> {
    minLength(min: number): this {
        return this.addRule({
            validate: value => value.length >= min,
            message: `Must be at least ${min} characters`,
        });
    }

    maxLength(max: number): this {
        return this.addRule({
            validate: value => value.length <= max,
            message: `Must be at most ${max} characters`,
        });
    }

    pattern(regex: RegExp, message: string): this {
        return this.addRule({
            validate: value => regex.test(value),
            message,
        });
    }

    email(): this {
        return this.pattern(/^[^\s@]+@[^\s@]+\.[^\s@]+$/, 'Must be a valid email');
    }
}

export class NumberValidator extends Validator<number> {
    min(min: number): this {
        return this.addRule({
            validate: value => value >= min,
            message: `Must be at least ${min}`,
        });
    }

    max(max: number): this {
        return this.addRule({
            validate: value => value <= max,
            message: `Must be at most ${max}`,
        });
    }

    integer(): this {
        return this.addRule({
            validate: value => Number.isInteger(value),
            message: 'Must be an integer',
        });
    }

    positive(): this {
        return this.addRule({
            validate: value => value > 0,
            message: 'Must be positive',
        });
    }
}

// Export all types for external use
export type { EventEmitter };
