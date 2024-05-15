#!/bin/bash
cargo clean
cargo clean --release
cargo build 
cargo build --release
cargo test --no-run
# edit stack on excutables
export RUST_LOG=info
cargo test -- --test-threads=1 --nocapture
cargo run --bin rust-define-global-allocator -- --nocapture
cargo run --bin rust-paragraph-allocator -- --nocapture
cargo test --release -- --test-threads=1 --nocapture
cargo run --release --bin rust-define-global-allocator -- --nocapture
cargo run --release --bin rust-paragraph-allocator -- --nocapture
export RUST_LOG=
