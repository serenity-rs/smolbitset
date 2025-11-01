[![ci-badge][]][ci] [![docs-badge][]][docs] [![crates.io version]][crates.io link] [![rust-version-badge]][rust-version-link]

# smolbitset

A library for dynamically sized bitsets with small storage optimization.

All values up to `usize::MAX >> 1` are stored without incurring any heap allocations.\
Any larger values dynamically allocate an appropriately sized `u32` slice on the heap.\
`SmolBitSet` also has a niche optimization so `Option<SmolBitSet>` and `SmolBitSet` have the same size of 1 `usize`.

[ci]: https://github.com/serenity-rs/smolbitset/actions
[ci-badge]: https://img.shields.io/github/actions/workflow/status/serenity-rs/smolbitset/ci.yml?branch=main&style=flat-square
[docs]: https://docs.rs/smolbitset
[docs-badge]: https://img.shields.io/badge/docs-online-5023dd.svg?style=flat-square
[crates.io link]: https://crates.io/crates/smolbitset
[crates.io version]: https://img.shields.io/crates/v/smolbitset.svg?style=flat-square
[rust-version-badge]: https://img.shields.io/badge/rust-1.89.0+-93450a.svg?style=flat-square
[rust-version-link]: https://blog.rust-lang.org/2025/08/07/Rust-1.89.0/
