<!-- Copyright © 2018–2021 Trevor Spiteri -->

<!-- Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved. This file is offered
as-is, without any warranty. -->

# Fixed-point numbers

The [*fixed* crate] provides fixed-point numbers.

  * [`FixedI8`] and [`FixedU8`] are eight-bit fixed-point numbers.
  * [`FixedI16`] and [`FixedU16`] are 16-bit fixed-point numbers.
  * [`FixedI32`] and [`FixedU32`] are 32-bit fixed-point numbers.
  * [`FixedI64`] and [`FixedU64`] are 64-bit fixed-point numbers.
  * [`FixedI128`] and [`FixedU128`] are 128-bit fixed-point numbers.

These types can have `Frac` fractional bits, where
0 ≤ `Frac` ≤ <i>n</i> and <i>n</i> is the total number of bits. When
`Frac` = 0, the fixed-point number behaves like an <i>n</i>-bit
integer. When `Frac` = <i>n</i>, the value <i>x</i> lies in the range
−0.5 ≤ <i>x</i> < 0.5 for signed numbers, and in the range
0 ≤ <i>x</i> < 1 for unsigned numbers.

In version 1 the [*typenum* crate] is used for the fractional bit
count `Frac`; the plan is to to have a major version 2 with [const
generics] instead when the Rust compiler support for them is powerful
enough.

The main features are

  * Representation of fixed-point numbers up to 128 bits wide.
  * Conversions between fixed-point numbers and numeric primitives.
  * Comparisons between fixed-point numbers and numeric primitives.
  * Parsing from strings in decimal, binary, octal and hexadecimal.
  * Display as decimal, binary, octal and hexadecimal.
  * Arithmetic and logic operations.

This crate does *not* provide general analytic functions.

  * No algebraic functions are provided, for example no `sqrt` or
    `pow`.
  * No trigonometric functions are provided, for example no `sin` or
    `cos`.
  * No other transcendental functions are provided, for example no
    `log` or `exp`.

These functions are not provided because different implementations can
have different trade-offs, for example trading some correctness for
speed. Implementations can be provided in other crates.

  * The [*fixed-sqrt* crate] provides the square root operation.

The conversions supported cover the following cases.

  * Infallible lossless conversions between fixed-point numbers and
    numeric primitives are provided using [`From`] and [`Into`]. These
    never fail (infallible) and do not lose any bits (lossless).
  * Infallible lossy conversions between fixed-point numbers and
    numeric primitives are provided using the [`LossyFrom`] and
    [`LossyInto`] traits. The source can have more fractional bits
    than the destination.
  * Checked lossless conversions between fixed-point numbers and
    numeric primitives are provided using the [`LosslessTryFrom`] and
    [`LosslessTryInto`] traits. The source cannot have more fractional
    bits than the destination.
  * Checked conversions between fixed-point numbers and numeric
    primitives are provided using the [`FromFixed`] and [`ToFixed`]
    traits, or using the [`from_num`] and [`to_num`] methods and
    [their checked versions][`checked_from_num`].
  * Fixed-point numbers can be parsed from decimal strings using
    [`FromStr`], and from binary, octal and hexadecimal strings using
    the [`from_str_binary`], [`from_str_octal`] and [`from_str_hex`]
    methods. The result is rounded to the nearest, with ties rounded
    to even.
  * Fixed-point numbers can be converted to strings using [`Display`],
    [`Binary`], [`Octal`], [`LowerHex`] and [`UpperHex`]. The output
    is rounded to the nearest, with ties rounded to even.

## What’s new

### Version 1.7.0 news (unreleased)

  * The following methods were added to all fixed-point numbers, to
    the [`Fixed`][tf-1-7] trait, and to the [`Wrapping`][w-1-7] and
    [`Unwrapped`][u-1-7] wrappers:
      * [`from_be`][f-fb-1-7], [`from_le`][f-fl-1-7]
      * [`to_be`][f-tb-1-7], [`to_le`][f-tl-1-7]
      * [`swap_bytes`][f-sb-1-7],
      * [`reverse_bits`][f-rb-1-7]
  * For the experimental feature [`num-traits`][feat-exp-1-7], the
    following traits were implemented where applicable:
      * [`OverflowingAdd`][nt-0-2-oa], [`OverflowingSub`][nt-0-2-os],
        [`OverflowingMul`][nt-0-2-om]

[f-fb-1-7]: https://tspiteri.gitlab.io/fixed/dev/fixed/struct.FixedI32.html#method.from_be
[f-fl-1-7]: https://tspiteri.gitlab.io/fixed/dev/fixed/struct.FixedI32.html#method.from_le
[f-rb-1-7]: https://tspiteri.gitlab.io/fixed/dev/fixed/struct.FixedI32.html#method.reverse_bits
[f-sb-1-7]: https://tspiteri.gitlab.io/fixed/dev/fixed/struct.FixedI32.html#method.swap_bytes
[f-tb-1-7]: https://tspiteri.gitlab.io/fixed/dev/fixed/struct.FixedI32.html#method.to_be
[f-tl-1-7]: https://tspiteri.gitlab.io/fixed/dev/fixed/struct.FixedI32.html#method.to_le
[feat-exp-1-7]: https://tspiteri.gitlab.io/fixed/dev/fixed/#experimental-optional-features
[nt-0-2-oa]: https://docs.rs/num-traits/^0.2/num_traits/ops/overflowing/trait.OverflowingAdd.html
[nt-0-2-om]: https://docs.rs/num-traits/^0.2/num_traits/ops/overflowing/trait.OverflowingMul.html
[nt-0-2-os]: https://docs.rs/num-traits/^0.2/num_traits/ops/overflowing/trait.OverflowingSub.html
[tf-1-7]: https://tspiteri.gitlab.io/fixed/dev/fixed/traits/trait.Fixed.html
[u-1-7]: https://tspiteri.gitlab.io/fixed/dev/fixed/struct.Unwrapped.html
[w-1-7]: https://tspiteri.gitlab.io/fixed/dev/fixed/struct.Wrapping.html

### Version 1.6.0 news (2021-02-05)

  * The crate now requires rustc version 1.47.0 or later.
  * The optional [*az* crate] dependency was updated to
    [version 1.1][az-1-1].
  * The [`unsigned_abs`][f-ua-1-6] method was added to all signed
    fixed-point types and to the [`FixedSigned`][tfs-1-6] trait.
  * The following methods are now `const` functions:
      * [`checked_neg`][f-cn-1-6], [`checked_add`][f-cad-1-6],
        [`checked_sub`][f-cs-1-6], [`checked_mul_int`][f-cmi-1-6],
        [`checked_shl`][f-cshl-1-6], [`checked_shr`][f-cshr-1-6],
        [`checked_abs`][f-cab-1-6]
  * The [`unwrapped_to_fixed`][f-utf-1-6] method was added to the
    [`ToFixed`][f-tf-1-6] trait.
  * The [`unwrapped_from_fixed`][f-uff-1-6] method was added to the
    [`FromFixed`][f-ff-1-6] trait.

[*az* crate]: https://crates.io/crates/az
[az-1-1]: https://docs.rs/az/~1.1/az/index.html
[f-cab-1-6]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.checked_abs
[f-cad-1-6]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.checked_add
[f-cmi-1-6]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.checked_mul_int
[f-cn-1-6]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.checked_neg
[f-cs-1-6]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.checked_sub
[f-cshl-1-6]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.checked_shl
[f-cshr-1-6]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.checked_shr
[f-ff-1-6]: https://docs.rs/fixed/~1.6/fixed/traits/trait.FromFixed.html
[f-tf-1-6]: https://docs.rs/fixed/~1.6/fixed/traits/trait.ToFixed.html
[f-ua-1-6]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.unsigned_abs
[f-uff-1-6]: https://docs.rs/fixed/~1.6/fixed/traits/trait.FromFixed.html#method.unwrapped_from_fixed
[f-utf-1-6]: https://docs.rs/fixed/~1.6/fixed/traits/trait.ToFixed.html#method.unwrapped_to_fixed
[tfs-1-6]: https://docs.rs/fixed/~1.6/fixed/traits/trait.FixedSigned.html

### Other releases

Details on other releases can be found in [*RELEASES.md*].

[*RELEASES.md*]: https://gitlab.com/tspiteri/fixed/blob/master/RELEASES.md

## Quick examples

```rust
use fixed::types::I20F12;

// 19/3 = 6 1/3
let six_and_third = I20F12::from_num(19) / 3;
// four decimal digits for 12 binary digits
assert_eq!(six_and_third.to_string(), "6.3333");
// find the ceil and convert to i32
assert_eq!(six_and_third.ceil().to_num::<i32>(), 7);
// we can also compare directly to integers
assert_eq!(six_and_third.ceil(), 7);
```

The type [`I20F12`] is a 32-bit fixed-point signed number with 20
integer bits and 12 fractional bits. It is an alias to
<code>[FixedI32][`FixedI32`]&lt;[U12][`U12`]&gt;</code>. The unsigned
counterpart would be [`U20F12`]. Aliases are provided for all
combinations of integer and fractional bits adding up to a total of
eight, 16, 32, 64 or 128 bits.

```rust
use fixed::types::{I4F4, I4F12};

// −8 ≤ I4F4 < 8 with steps of 1/16 (~0.06)
let a = I4F4::from_num(1);
// multiplication and division by integers are possible
let ans1 = a / 5 * 17;
// 1 / 5 × 17 = 3 2/5 (3.4), but we get 3 3/16 (~3.2)
assert_eq!(ans1, I4F4::from_bits((3 << 4) + 3));
assert_eq!(ans1.to_string(), "3.2");

// −8 ≤ I4F12 < 8 with steps of 1/4096 (~0.0002)
let wider_a = I4F12::from(a);
let wider_ans = wider_a / 5 * 17;
let ans2 = I4F4::from_num(wider_ans);
// now the answer is the much closer 3 6/16 (~3.4)
assert_eq!(ans2, I4F4::from_bits((3 << 4) + 6));
assert_eq!(ans2.to_string(), "3.4");
```

The second example shows some precision and conversion issues. The low
precision of `a` means that `a / 5` is 3⁄16 instead of 1⁄5, leading to
an inaccurate result `ans1` = 3 3⁄16 (~3.2). With a higher precision,
we get `wider_a / 5` equal to 819⁄4096, leading to a more accurate
intermediate result `wider_ans` = 3 1635⁄4096. When we convert back to
four fractional bits, we get `ans2` = 3 6⁄16 (~3.4).

Note that we can convert from [`I4F4`] to [`I4F12`] using [`From`], as
the target type has the same number of integer bits and a larger
number of fractional bits. Converting from [`I4F12`] to [`I4F4`]
cannot use [`From`] as we have less fractional bits, so we use
[`from_num`] instead.

## Writing fixed-point constants and values literally

The [*fixed-macro* crate] provides a convenient macro to write down
fixed-point constants literally in the code.

```rust
use fixed::types::I16F16;
use fixed_macro::fixed;

const NUM1: I16F16 = fixed!(12.75: I16F16);
let num2 = NUM1 + fixed!(13.125: I16F16);
assert_eq!(num2, 25.875);
```

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use
it in your crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "1.6"
```

The *fixed* crate requires rustc version 1.47.0 or later.

## Optional features

The *fixed* crate has these optional feature:

 1. `az`, disabled by default. This implements the cast traits
    provided by the [*az* crate].
 2. `f16`, disabled by default. This provides conversion to/from
    [`f16`] and [`bf16`]. This features requires the [*half* crate].
 3. `serde`, disabled by default. This provides serialization support
    for the fixed-point types. This feature requires the
    [*serde* crate].
 4. `std`, disabled by default. This is for features that are not
    possible under `no_std`: currently the implementation of the
    [`Error`] trait for [`ParseFixedError`].
 5. `serde-str`, disabled by default. Fixed-point numbers are
    serialized as strings showing the value when using human-readable
    formats. This feature requires the `serde` and the `std` optional
    features. **Warning:** numbers serialized when this feature is
    enabled cannot be deserialized when this feature is disabled, and
    vice versa.

To enable features, you can add the dependency like this to
[*Cargo.toml*]:

```toml
[dependencies.fixed]
version = "1.6"
features = ["f16", "serde"]
```

## Experimental optional features

It is not considered a breaking change if experimental features are
removed. The removal of experimental features would however require a
minor version bump. Similarly, on a minor version bump, optional
dependencies can be updated to an incompatible newer version.

There is one experimental feature:

 1. `num-traits`, disabled by default. This implements some traits
    from the [*num-traits* crate]. (The plan is to upgrade this to an
    optional feature once the [*num-traits* crate] reaches version
    1.0.0.)

## License

This crate is free software: you can redistribute it and/or modify it
under the terms of either

  * the [Apache License, Version 2.0][LICENSE-APACHE] or
  * the [MIT License][LICENSE-MIT]

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache
License, Version 2.0, shall be dual licensed as above, without any
additional terms or conditions.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*az* crate]: https://crates.io/crates/az
[*fixed* crate]: https://crates.io/crates/fixed
[*fixed-macro* crate]: https://crates.io/crates/fixed-macro
[*fixed-sqrt* crate]: https://crates.io/crates/fixed-sqrt
[*half* crate]: https://crates.io/crates/half
[*num-traits* crate]: https://crates.io/crates/num-traits
[*serde* crate]: https://crates.io/crates/serde
[*typenum* crate]: https://crates.io/crates/typenum
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[`Binary`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Binary.html
[`Display`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Display.html
[`Error`]: https://doc.rust-lang.org/nightly/std/error/trait.Error.html
[`FixedI128`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI128.html
[`FixedI16`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI16.html
[`FixedI32`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html
[`FixedI64`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI64.html
[`FixedI8`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI8.html
[`FixedU128`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedU128.html
[`FixedU16`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedU16.html
[`FixedU32`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedU32.html
[`FixedU64`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedU64.html
[`FixedU8`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedU8.html
[`FromFixed`]: https://docs.rs/fixed/~1.6/fixed/traits/trait.FromFixed.html
[`FromStr`]: https://doc.rust-lang.org/nightly/core/str/trait.FromStr.html
[`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
[`I20F12`]: https://docs.rs/fixed/~1.6/fixed/types/type.I20F12.html
[`I4F12`]: https://docs.rs/fixed/~1.6/fixed/types/type.I4F12.html
[`I4F4`]: https://docs.rs/fixed/~1.6/fixed/types/type.I4F4.html
[`Into`]: https://doc.rust-lang.org/nightly/core/convert/trait.Into.html
[`LosslessTryFrom`]: https://docs.rs/fixed/~1.6/fixed/traits/trait.LosslessTryFrom.html
[`LosslessTryInto`]: https://docs.rs/fixed/~1.6/fixed/traits/trait.LosslessTryInto.html
[`LossyFrom`]: https://docs.rs/fixed/~1.6/fixed/traits/trait.LossyFrom.html
[`LossyInto`]: https://docs.rs/fixed/~1.6/fixed/traits/trait.LossyInto.html
[`LowerHex`]: https://doc.rust-lang.org/nightly/core/fmt/trait.LowerHex.html
[`Octal`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Octal.html
[`ParseFixedError`]: https://docs.rs/fixed/~1.6/fixed/struct.ParseFixedError.html
[`ToFixed`]: https://docs.rs/fixed/~1.6/fixed/traits/trait.ToFixed.html
[`U12`]: https://docs.rs/fixed/~1.6/fixed/types/extra/type.U12.html
[`U20F12`]: https://docs.rs/fixed/~1.6/fixed/types/type.U20F12.html
[`UpperHex`]: https://doc.rust-lang.org/nightly/core/fmt/trait.UpperHex.html
[`bf16`]: https://docs.rs/half/^1/half/struct.bf16.html
[`checked_from_num`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.checked_from_num
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[`from_num`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.from_num
[`from_str_binary`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.from_str_binary
[`from_str_hex`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.from_str_hex
[`from_str_octal`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.from_str_octal
[`to_num`]: https://docs.rs/fixed/~1.6/fixed/struct.FixedI32.html#method.to_num
[const generics]: https://github.com/rust-lang/rust/issues/44580
