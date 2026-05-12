[![crates.io version]][crates.io link] [![ci-badge][]][ci] [![docs-badge][]][docs] [![rust-version-badge]][rust-version-link] [![license badge]][license]

# smolbitset

A crate for dynamically sized bitsets with memory usage optimizations.\
Supports 64 and 32 bit targets and has integrations with `serde` and `typesize`.\
For `no_std` support disable the default `std` feature. The `no_std` environment must support `alloc`.

Bitsets are stored in 2 different modes: inline without any allocations or on the heap.\
Additionally inline mode has 2 different encodings: normal and sparse.\
Normal encoding stores a regular bitset in a `usize` (minus the needed bits for mode and encoding flags).\
Sparse encoding stores a single bit index which allows for `const` construction of flag bitsets exceeding the inline bitset capacity.\
Heap mode does not support sparse encoding (yet, support may be added in the future).

| Pointer Size | `size_of::<SmolBitSet>` | Inline Capacity | Max Inline Sparse Bit |  Max Heap Capacity  |
|-------------:|------------------------:|----------------:|----------------------:|--------------------:|
| 32 bits      | 4 bytes                 | 30 bits         | 1 073 741 824 (2^30)    | 2^37 bits (~17.1GB) |
| 64 bits      | 8 bytes                 | 62 bits         | 4 294 967 296 (2^32)    | 2^37 bits (~17.1GB) |

Furthermore `SmolBitSet` has a niche optimization so `Option<SmolBitSet>` has the same size as `SmolBitSet`.

## Limitations

`SmolBitSet` can not implement `Copy`.\
Implementing `core::ops::Not` is also not possible (or rather complex).\
Related alternative methods are provided via `SmolBitSet::and_not` and `SmolBitSet::and_not_assign`.

## Example

```rust
use smolbitset::SmolBitSet;

let mut sbs = SmolBitSet::new();

sbs |= 1u32 << 5;
sbs >>= 5u8;
assert_eq!(sbs, SmolBitSet::from(1u64));

sbs |= !1u64;
assert_eq!(sbs, SmolBitSet::from(u64::MAX));

sbs <<= 64u16;
assert_eq!(sbs, SmolBitSet::from_bits(&(64..128).collect::<Box<[_]>>()))
```

## Minimum Supported Rust Version

This is currently `1.89`, and is considered a breaking change to increase.

[ci]: https://github.com/serenity-rs/smolbitset/actions
[ci-badge]: https://img.shields.io/github/actions/workflow/status/serenity-rs/smolbitset/ci.yml?branch=main&style=flat-square
[docs]: https://docs.rs/smolbitset
[docs-badge]: https://img.shields.io/docsrs/smolbitset/latest?style=flat-square
[crates.io link]: https://crates.io/crates/smolbitset
[crates.io version]: https://img.shields.io/crates/v/smolbitset.svg?style=flat-square
[rust-version-badge]: https://img.shields.io/badge/rust-1.89.0+-93450a.svg?style=flat-square
[rust-version-link]: https://blog.rust-lang.org/2025/08/07/Rust-1.89.0/
[license]: LICENSE
[license badge]: https://img.shields.io/crates/l/poise.svg?style=flat-square&color=yellow
