<!-- Copyright © 2018–2022 Trevor Spiteri -->

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

An <i>n</i>-bit fixed-point number has <i>f</i>&nbsp;=&nbsp;`Frac` fractional
bits where 0&nbsp;≤&nbsp;<i>f</i>&nbsp;≤&nbsp;<i>n</i>, and
<i>n</i>&nbsp;&minus;&nbsp;<i>f</i> integer bits. For example,
<code>[FixedI32]\<[U24]></code> is a 32-bit signed fixed-point number with
<i>n</i>&nbsp;=&nbsp;32 total bits, <i>f</i>&nbsp;=&nbsp;24 fractional bits, and
<i>n</i>&nbsp;&minus;&nbsp;<i>f</i>&nbsp;=&nbsp;8 integer bits.
<code>[FixedI32]\<[U0]></code> behaves like [`i32`], and
<code>[FixedU32]\<[U0]></code> behaves like [`u32`].

The difference between any two successive representable numbers is constant
throughout the possible range for a fixed-point number:
<i>Δ</i>&nbsp;=&nbsp;1/2<sup><i>f</i></sup>. When <i>f</i>&nbsp;=&nbsp;0, like
in <code>[FixedI32]\<[U0]></code>, <i>Δ</i>&nbsp;=&nbsp;1 because representable
numbers are integers, and the difference between two successive integers is 1.
When <i>f</i>&nbsp;=&nbsp;<i>n</i>, <i>Δ</i>&nbsp;=&nbsp;1/2<sup><i>n</i></sup>
and the value lies in the range &minus;0.5&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;0.5
for signed numbers like <code>[FixedI32]\<[U32]></code>, and in the range
0&nbsp;≤&nbsp;<i>x</i>&nbsp;<&nbsp;1 for unsigned numbers like
<code>[FixedU32]\<[U32]></code>.

In version 1 the [*typenum* crate] is used for the fractional bit count `Frac`;
the plan is to to have a major version 2 with const generics when the Rust
compiler’s [`generic_const_expr` feature] is ready and stabilized. An [alpha
version] is already available.

[`generic_const_expr` feature]: https://github.com/rust-lang/rust/issues/76560
[alpha version]: https://crates.io/crates/fixed/2.0.0-alpha.2

The main features are

  * Representation of binary fixed-point numbers up to 128 bits wide.
  * Conversions between fixed-point numbers and numeric primitives.
  * Comparisons between fixed-point numbers and numeric primitives.
  * Parsing from strings in decimal, binary, octal and hexadecimal.
  * Display as decimal, binary, octal and hexadecimal.
  * Arithmetic and logic operations.

This crate does *not* provide decimal fixed-point numbers. For example 0.001
cannot be represented exactly, as it is 1/10<sup>3</sup>. It is binary fractions
like 1/2<sup>4</sup> (0.0625) that can be represented exactly, provided there
are enough fractional bits.

This crate does *not* provide general analytic functions.

  * No algebraic functions are provided, for example no `sqrt` or `pow`.
  * No trigonometric functions are provided, for example no `sin` or `cos`.
  * No other transcendental functions are provided, for example no `log` or
    `exp`.

These functions are not provided because different implementations can have
different trade-offs, for example trading some correctness for speed.
Implementations can be provided in other crates.

  * The [*fixed-sqrt* crate] provides the square root operation.
  * The [*cordic* crate] provides various functions implemented using the
    [CORDIC] algorithm.

The conversions supported cover the following cases.

  * Infallible lossless conversions between fixed-point numbers and numeric
    primitives are provided using [`From`] and [`Into`]. These never fail
    (infallible) and do not lose any bits (lossless).
  * Infallible lossy conversions between fixed-point numbers and numeric
    primitives are provided using the [`LossyFrom`] and [`LossyInto`] traits.
    The source can have more fractional bits than the destination.
  * Checked lossless conversions between fixed-point numbers and numeric
    primitives are provided using the [`LosslessTryFrom`] and
    [`LosslessTryInto`] traits. The source cannot have more fractional bits than
    the destination.
  * Checked conversions between fixed-point numbers and numeric primitives are
    provided using the [`FromFixed`] and [`ToFixed`] traits, or using the
    [`from_num`] and [`to_num`] methods and [their checked
    versions][`checked_from_num`].
  * Additionally, [`az`] casts are implemented for conversion between
    fixed-point nubmers and numeric primitives.
  * Fixed-point numbers can be parsed from decimal strings using [`FromStr`],
    and from binary, octal and hexadecimal strings using the
    [`from_str_binary`], [`from_str_octal`] and [`from_str_hex`] methods. The
    result is rounded to the nearest, with ties rounded to even.
  * Fixed-point numbers can be converted to strings using [`Display`],
    [`Binary`], [`Octal`], [`LowerHex`] and [`UpperHex`]. The output is rounded
    to the nearest, with ties rounded to even.
  * All fixed-point numbers are plain old data, so [`bytemuck`] bit casting
    conversions can be used.

## What’s new

### Version 1.14.0 news (2022-03-20)

  * The [`next_multiple_of`][f-nmo-1-14] method was added to all fixed-point
    numbers, to the [`Fixed`][tf-1-14] trait, and to the [`Wrapping`][w-1-14]
    and [`Unwrapped`][u-1-14] wrappers.
  * The following methods were added to all fixed-point numbers and to the
    [`Fixed`][tf-1-14] trait:
      * [`abs_diff`][f-ad-1-14]
      * [`checked_next_multiple_of`][f-cnmo-1-14],
        [`saturating_next_multiple_of`][f-snmo-1-14],
        [`wrapping_next_multiple_of`][f-wnmo-1-14],
        [`unwrapped_next_multiple_of`][f-unmo-1-14],
        [`overflowing_next_multiple_of`][f-onmo-1-14]
  * The following methods were added to all signed fixed-point numbers, to the
    [`FixedSigned`][tfs-1-14] trait, and to the [`Wrapping`][w-1-14] and
    [`Unwrapped`][u-1-14] wrappers for signed numbers:
      * [`add_unsigned`][f-au-1-14], [`sub_unsigned`][f-su-1-14]
      * [`checked_add_unsigned`][f-cau-1-14],
        [`saturating_add_unsigned`][f-sau-1-14],
        [`wrapping_add_unsigned`][f-wau-1-14],
        [`unwrapped_add_unsigned`][f-uau-1-14],
        [`overflowing_add_unsigned`][f-oau-1-14]
      * [`checked_sub_unsigned`][f-csu-1-14],
        [`saturating_sub_unsigned`][f-ssu-1-14],
        [`wrapping_sub_unsigned`][f-wsu-1-14],
        [`unwrapped_sub_unsigned`][f-usu-1-14],
        [`overflowing_sub_unsigned`][f-osu-1-14]
  * The following methods were added to all unsigned fixed-point numbers, to the
    [`FixedUnsigned`][tfu-1-14] trait, and to the [`Wrapping`][w-1-14] and
    [`Unwrapped`][u-1-14] wrappers for unsigned numbers:
      * [`add_signed`][f-as-1-14], [`sub_signed`][f-ss-1-14]
      * [`checked_add_signed`][f-cas-1-14],
        [`saturating_add_signed`][f-sas-1-14],
        [`wrapping_add_signed`][f-was-1-14],
        [`unwrapped_add_signed`][f-uas-1-14],
        [`overflowing_add_signed`][f-oas-1-14]
      * [`checked_sub_signed`][f-css-1-14],
        [`saturating_sub_signed`][f-sss-1-14],
        [`wrapping_sub_signed`][f-wss-1-14],
        [`unwrapped_sub_signed`][f-uss-1-14],
        [`overflowing_sub_signed`][f-oss-1-14]
  * Supertraits were added to <code>[Fixed][tf-1-14]::[Bits][tf-b-1-14]</code>
    and to <code>[Fixed][tf-1-14]::[NonZeroBits][tf-nzb-1-14]</code> in order to
    allow conversions and operations in generic functions.
  * The [*az* crate] dependency was updated to [version 1.2][az-1-2].

[*az* crate]: https://crates.io/crates/az
[az-1-2]: https://docs.rs/az/~1.2/az/index.html
[f-ad-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.abs_diff
[f-as-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html#method.add_signed
[f-au-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.add_unsigned
[f-cas-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html#method.checked_add_signed
[f-cau-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.checked_add_unsigned
[f-cnmo-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.checked_next_multiple_of
[f-css-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html#method.checked_sub_signed
[f-csu-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.checked_sub_unsigned
[f-nmo-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.next_multiple_of
[f-oas-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html#method.overflowing_add_signed
[f-oau-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.overflowing_add_unsigned
[f-onmo-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.overflowing_next_multiple_of
[f-oss-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html#method.overflowing_sub_signed
[f-osu-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.overflowing_sub_unsigned
[f-sas-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html#method.saturating_add_signed
[f-sau-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.saturating_add_unsigned
[f-snmo-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.saturating_next_multiple_of
[f-ss-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html#method.sub_signed
[f-sss-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html#method.saturating_sub_signed
[f-ssu-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.saturating_sub_unsigned
[f-su-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.sub_unsigned
[f-uas-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html#method.unwrapped_add_signed
[f-uau-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.unwrapped_add_unsigned
[f-unmo-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.unwrapped_next_multiple_of
[f-uss-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html#method.unwrapped_sub_signed
[f-usu-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.unwrapped_sub_unsigned
[f-was-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html#method.wrapping_add_signed
[f-wau-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.wrapping_add_unsigned
[f-wnmo-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.wrapping_next_multiple_of
[f-wss-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html#method.wrapping_sub_signed
[f-wsu-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.wrapping_sub_unsigned
[tf-1-14]: https://docs.rs/fixed/~1.14/fixed/traits/trait.Fixed.html
[tf-b-1-14]: https://docs.rs/fixed/~1.14/fixed/traits/trait.Fixed.html#associatedtype.Bits
[tf-nzb-1-14]: https://docs.rs/fixed/~1.14/fixed/traits/trait.Fixed.html#associatedtype.NonZeroBits
[tfs-1-14]: https://docs.rs/fixed/~1.14/fixed/traits/trait.FixedSigned.html
[tfu-1-14]: https://docs.rs/fixed/~1.14/fixed/traits/trait.FixedUnsigned.html
[u-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.Unwrapped.html
[w-1-14]: https://docs.rs/fixed/~1.14/fixed/struct.Wrapping.html

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

The type [`I20F12`] is a 32-bit fixed-point signed number with 20 integer bits
and 12 fractional bits. It is an alias to <code>[FixedI32]\<[U12]></code>. The
unsigned counterpart would be [`U20F12`]. Aliases are provided for all
combinations of integer and fractional bits adding up to a total of eight, 16,
32, 64 or 128 bits.

```rust
use fixed::types::{I4F4, I4F12};

// -8 ≤ I4F4 < 8 with steps of 1/16 (~0.06)
let a = I4F4::from_num(1);
// multiplication and division by integers are possible
let ans1 = a / 5 * 17;
// 1 / 5 × 17 = 3 2/5 (3.4), but we get 3 3/16 (~3.2)
assert_eq!(ans1, I4F4::from_bits((3 << 4) + 3));
assert_eq!(ans1.to_string(), "3.2");

// -8 ≤ I4F12 < 8 with steps of 1/4096 (~0.0002)
let wider_a = I4F12::from(a);
let wider_ans = wider_a / 5 * 17;
let ans2 = I4F4::from_num(wider_ans);
// now the answer is the much closer 3 6/16 (~3.4)
assert_eq!(ans2, I4F4::from_bits((3 << 4) + 6));
assert_eq!(ans2.to_string(), "3.4");
```

The second example shows some precision and conversion issues. The low precision
of `a` means that `a / 5` is 3⁄16 instead of 1⁄5, leading to an inaccurate
result `ans1` = 3 3⁄16 (~3.2). With a higher precision, we get `wider_a / 5`
equal to 819⁄4096, leading to a more accurate intermediate result `wider_ans` =
3 1635⁄4096. When we convert back to four fractional bits, we get `ans2` = 3
6⁄16 (~3.4).

Note that we can convert from [`I4F4`] to [`I4F12`] using [`From`], as the
target type has the same number of integer bits and a larger number of
fractional bits. Converting from [`I4F12`] to [`I4F4`] cannot use [`From`] as we
have less fractional bits, so we use [`from_num`] instead.

## Writing fixed-point constants and values literally

The [*fixed-macro* crate] provides a convenient macro to write down fixed-point
constants literally in the code.

```rust
use fixed::types::I16F16;
use fixed_macro::fixed;

const NUM1: I16F16 = fixed!(12.75: I16F16);
let num2 = NUM1 + fixed!(13.125: I16F16);
assert_eq!(num2, 25.875);
```

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use it in your
crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "1.14"
```

The *fixed* crate requires rustc version 1.57.0 or later.

## Optional features

The *fixed* crate has these optional feature:

 1. `arbitrary`, disabled by default. This provides the generation of arbitrary
    fixed-point numbers from raw, unstructured data. This feature requires the
    [*arbitrary* crate].
 2. `serde`, disabled by default. This provides serialization support for the
    fixed-point types. This feature requires the [*serde* crate].
 3. `std`, disabled by default. This is for features that are not possible under
    `no_std`: currently the implementation of the [`Error`] trait for
    [`ParseFixedError`].
 4. `serde-str`, disabled by default. Fixed-point numbers are serialized as
    strings showing the value when using human-readable formats. This feature
    requires the `serde` and the `std` optional features. **Warning:** numbers
    serialized when this feature is enabled cannot be deserialized when this
    feature is disabled, and vice versa.

To enable features, you can add the dependency like this to [*Cargo.toml*]:

```toml
[dependencies.fixed]
version = "1.14"
features = ["serde"]
```

## Experimental optional features

It is not considered a breaking change if the following experimental features
are removed. The removal of experimental features would however require a minor
version bump. Similarly, on a minor version bump, optional dependencies can be
updated to an incompatible newer version.

 1. `borsh`, disabled by default. This implements serialization and
    deserialization using the [*borsh* crate]. (The plan is to promote this to
    an optional feature once the [*borsh* crate] reaches version 1.0.0.)
 2. `num-traits`, disabled by default. This implements some traits from the
    [*num-traits* crate]. (The plan is to promote this to an optional feature
    once the [*num-traits* crate] reaches version 1.0.0.)

## Deprecated optional features

The following optional features are deprecated and will be removed in the next
major version of the crate.

 1. `az`, has no effect. Previously required for the [`az`] cast traits. Now
    these cast traits are always provided.
 2. `f16`, has no effect. Previously required for conversion to/from [`f16`] and
    [`bf16`]. Now these conversions are always provided.

## License

This crate is free software: you can redistribute it and/or modify it under the
terms of either

  * the [Apache License, Version 2.0][LICENSE-APACHE] or
  * the [MIT License][LICENSE-MIT]

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache License, Version 2.0,
shall be dual licensed as above, without any additional terms or conditions.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*arbitrary* crate]: https://crates.io/crates/arbitrary
[*borsh* crate]: https://crates.io/crates/borsh
[*cordic* crate]: https://crates.io/crates/cordic
[*fixed* crate]: https://crates.io/crates/fixed
[*fixed-macro* crate]: https://crates.io/crates/fixed-macro
[*fixed-sqrt* crate]: https://crates.io/crates/fixed-sqrt
[*half* crate]: https://crates.io/crates/half
[*num-traits* crate]: https://crates.io/crates/num-traits
[*serde* crate]: https://crates.io/crates/serde
[*typenum* crate]: https://crates.io/crates/typenum
[CORDIC]: https://en.wikipedia.org/wiki/CORDIC
[FixedI32]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html
[FixedU32]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[U0]: https://docs.rs/fixed/~1.14/fixed/types/extra/type.U0.html
[U12]: https://docs.rs/fixed/~1.14/fixed/types/extra/type.U12.html
[U24]: https://docs.rs/fixed/~1.14/fixed/types/extra/type.U24.html
[U32]: https://docs.rs/fixed/~1.14/fixed/types/extra/type.U32.html
[`Binary`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Binary.html
[`Display`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Display.html
[`Error`]: https://doc.rust-lang.org/nightly/std/error/trait.Error.html
[`FixedI128`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI128.html
[`FixedI16`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI16.html
[`FixedI32`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html
[`FixedI64`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI64.html
[`FixedI8`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI8.html
[`FixedU128`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU128.html
[`FixedU16`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU16.html
[`FixedU32`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU32.html
[`FixedU64`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU64.html
[`FixedU8`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedU8.html
[`FromFixed`]: https://docs.rs/fixed/~1.14/fixed/traits/trait.FromFixed.html
[`FromStr`]: https://doc.rust-lang.org/nightly/core/str/trait.FromStr.html
[`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
[`I20F12`]: https://docs.rs/fixed/~1.14/fixed/types/type.I20F12.html
[`I4F12`]: https://docs.rs/fixed/~1.14/fixed/types/type.I4F12.html
[`I4F4`]: https://docs.rs/fixed/~1.14/fixed/types/type.I4F4.html
[`Into`]: https://doc.rust-lang.org/nightly/core/convert/trait.Into.html
[`LosslessTryFrom`]: https://docs.rs/fixed/~1.14/fixed/traits/trait.LosslessTryFrom.html
[`LosslessTryInto`]: https://docs.rs/fixed/~1.14/fixed/traits/trait.LosslessTryInto.html
[`LossyFrom`]: https://docs.rs/fixed/~1.14/fixed/traits/trait.LossyFrom.html
[`LossyInto`]: https://docs.rs/fixed/~1.14/fixed/traits/trait.LossyInto.html
[`LowerHex`]: https://doc.rust-lang.org/nightly/core/fmt/trait.LowerHex.html
[`Octal`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Octal.html
[`ParseFixedError`]: https://docs.rs/fixed/~1.14/fixed/struct.ParseFixedError.html
[`ToFixed`]: https://docs.rs/fixed/~1.14/fixed/traits/trait.ToFixed.html
[`U20F12`]: https://docs.rs/fixed/~1.14/fixed/types/type.U20F12.html
[`UpperHex`]: https://doc.rust-lang.org/nightly/core/fmt/trait.UpperHex.html
[`az`]: https://docs.rs/az/^1/az/index.html
[`bf16`]: https://docs.rs/half/^1/half/struct.bf16.html
[`bytemuck`]: https://docs.rs/bytemuck/^1/bytemuck/index.html
[`checked_from_num`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.checked_from_num
[`f16`]: https://docs.rs/half/^1/half/struct.f16.html
[`from_num`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.from_num
[`from_str_binary`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.from_str_binary
[`from_str_hex`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.from_str_hex
[`from_str_octal`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.from_str_octal
[`i32`]: https://doc.rust-lang.org/nightly/core/primitive.i32.html
[`to_num`]: https://docs.rs/fixed/~1.14/fixed/struct.FixedI32.html#method.to_num
[`u32`]: https://doc.rust-lang.org/nightly/core/primitive.u32.html
