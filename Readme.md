# Memory Allocators in Rust

This project was created with the following command:
```
cargo init rust-allocators --lib
cd rust-allocators
```

We now create an executable as part of it with the following commands:
```
using vscode, create the filename `src/bin/rust-define-global-alloc.rs`
```

In this file we will create a memory allocator and use it. But before that, let's understand some basic concepts.

## Memory Basic Concepts

In a Rust program, the standard library has one “global” memory allocator. This allocator is used by default for types like Box<T> and Vec<T>.

**Key Concept** when the source defines an instance of a struct, it is created on the stack

```rust
#[derive(Drop)]     // tells rust to provide a default drop() trait implementation for our class
struct MyClass {
    member_data: i64,
}

// my_class_instance_on_stack is defined on the stack of the function that executes this statement
// it's lifetime ends once the current scope ends, which means MyClass::Drop gets called
let my_class_instance_on_stack = MyClass { 1i64 };
```

**Key Concept** when the source defines an instance of a boxed struct (i.e. Box<MyClass>), it is created in the process heap.  
This is done by calling the allocator on Box<T>::new() with the size_of::(struct MyClass) and then using the memory reference returned to instantiated Box<MyClass> in it.

```rust
// my_class_instance_in_the_heap is defined in the process heap
// it's lifetime ends once the current scope ends, which means it will be deleted from the heap when Box<MyClass>::Drop() gets called
let my_class_instance_in_the_heap = Box<MyClass>::new( MyClass { 2i64 } );
```

**Key Concept** from Rust point of view, both `my_class_instance_on_stack` and `my_class_instance_in_the_heap` are references to memory addresses.  
The address of the first happens to be in the stack region, the address of the second, happens to be within the memory pages allocated for the heap.
The only other difference is that both of these expressions are valid:
```rust
  assert_eq!(my_class_instance_on_stack.member_data, 1i64);
  assert_eq!(my_class_instance_in_the_heap.member_data, 2i64);
´´´

## Rust Memory Allocators

So, recapping: In a Rust program, the standard library has one “global” memory allocator. This allocator is used by default for types like Box<T> and Vec<T>.

The default global allocator is unspecified, but libraries (such as cdylibs and staticlibs) are guaranteed to use the System allocator by default.
You can configure the choice of global allocator using the #[global_allocator] attribute.
To implement a custom global allocator, you can create a type that implements the GlobalAlloc trait. This allows you to route all default allocation requests to your custom object.

Example of a custom allocator can be see in our source [rust-define-global-allocator.rs](./src/rust-define-global-allocator.rs) file contains an implementation of the Rust GlobalAlloc trait which is what Rust calls an interface.

```
# you can run both of theses executable examples
cargo run --bin rust-define-global-allocator
cargo run --bin rust-using-custom-allocator
```



