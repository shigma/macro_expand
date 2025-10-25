# macro_expand
 
[![Crates.io](https://img.shields.io/crates/v/macro_expand.svg)](https://crates.io/crates/macro_expand)
[![Documentation](https://docs.rs/macro_expand/badge.svg)](https://docs.rs/macro_expand)

A Rust library for expanding procedural macros in-place. It allows you to register custom procedural macros and apply them to Rust source code programmatically. This is particularly useful for testing procedural macros by comparing their output against expected snapshots.

## Installation
 
Add to your `Cargo.toml`:
 
```toml
[dependencies]
macro_expand = { version = "0.1" }
```
