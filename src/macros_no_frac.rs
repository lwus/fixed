// Copyright © 2018–2021 Trevor Spiteri

// This library is free software: you can redistribute it and/or
// modify it under the terms of either
//
//   * the Apache License, Version 2.0 or
//   * the MIT License
//
// at your option.
//
// You should have recieved copies of the Apache License and the MIT
// License along with the library. If not, see
// <https://www.apache.org/licenses/LICENSE-2.0> and
// <https://opensource.org/licenses/MIT>.

macro_rules! fixed_no_frac {
    (
        $Fixed:ident[$s_fixed:expr]($Inner:ty[$s_inner:expr], $LeEqU:tt, $s_nbits:expr),
        $nbytes:expr, $bytes_val:expr, $rev_bytes_val:expr, $be_bytes:expr, $le_bytes:expr,
        $UFixed:ident[$s_ufixed:expr], $UInner:ty, $Signedness:tt,
        $Double:ident, $DoubleInner:ty, $HasDouble:tt
    ) => {
        /// The implementation of items in this block is independent
        /// of the number of fractional bits `Frac`.
        impl<Frac> $Fixed<Frac> {
            comment! {
                "The smallest value that can be represented.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::MIN, Fix::from_bits(", $s_inner, "::MIN));
```
";
                pub const MIN: $Fixed<Frac> = Self::from_bits(<$Inner>::MIN);
            }

            comment! {
                "The largest value that can be represented.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::MAX, Fix::from_bits(", $s_inner, "::MAX));
```
";
                pub const MAX: $Fixed<Frac> = Self::from_bits(<$Inner>::MAX);
            }

            comment! {
                "Creates a fixed-point number that has a bitwise
representation identical to the given integer.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 0010.0000 == 2
assert_eq!(Fix::from_bits(0b10_0000), 2);
```
";
                #[inline]
                pub const fn from_bits(bits: $Inner) -> $Fixed<Frac> {
                    $Fixed {
                        bits,
                        phantom: PhantomData,
                    }
                }
            }

            comment! {
                "Creates an integer that has a bitwise representation
identical to the given fixed-point number.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 2 is 0010.0000
assert_eq!(Fix::from_num(2).to_bits(), 0b10_0000);
```
";
                #[inline]
                pub const fn to_bits(self) -> $Inner {
                    self.bits
                }
            }

            comment! {
                "Converts a fixed-point number from big endian to the target’s endianness.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let f = Fix::from_bits(", $bytes_val, ");
if cfg!(target_endian = \"big\") {
    assert_eq!(Fix::from_be(f), f);
} else {
    assert_eq!(Fix::from_be(f), f.swap_bytes());
}
```
";
                #[inline]
                pub const fn from_be(f: $Fixed<Frac>) -> $Fixed<Frac> {
                    $Fixed::from_bits(<$Inner>::from_be(f.to_bits()))
                }
            }

            comment! {
                "Converts a fixed-point number from little endian to the target’s endianness.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let f = Fix::from_bits(", $bytes_val, ");
if cfg!(target_endian = \"little\") {
    assert_eq!(Fix::from_le(f), f);
} else {
    assert_eq!(Fix::from_le(f), f.swap_bytes());
}
```
";
                #[inline]
                pub const fn from_le(f: $Fixed<Frac>) -> $Fixed<Frac> {
                    $Fixed::from_bits(<$Inner>::from_le(f.to_bits()))
                }
            }

            comment! {
                "Converts `self` to big endian from the target’s endianness.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let f = Fix::from_bits(", $bytes_val, ");
if cfg!(target_endian = \"big\") {
    assert_eq!(f.to_be(), f);
} else {
    assert_eq!(f.to_be(), f.swap_bytes());
}
```
";
                #[inline]
                pub const fn to_be(self) -> $Fixed<Frac> {
                    $Fixed::from_bits(self.to_bits().to_be())
                }
            }

            comment! {
                "Converts `self` to little endian from the target’s endianness.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let f = Fix::from_bits(", $bytes_val, ");
if cfg!(target_endian = \"little\") {
    assert_eq!(f.to_le(), f);
} else {
    assert_eq!(f.to_le(), f.swap_bytes());
}
```
";
                #[inline]
                pub const fn to_le(self) -> $Fixed<Frac> {
                    $Fixed::from_bits(self.to_bits().to_le())
                }
            }

            comment! {
                "Reverses the byte order of the fixed-point number.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let f = Fix::from_bits(", $bytes_val, ");
let swapped = Fix::from_bits(", $rev_bytes_val, ");
assert_eq!(f.swap_bytes(), swapped);
```
";
                #[inline]
                pub const fn swap_bytes(self) -> $Fixed<Frac> {
                    $Fixed::from_bits(self.to_bits().swap_bytes())
                }
            }

            comment! {
                "Creates a fixed-point number from its representation
as a byte array in big endian.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(
    Fix::from_be_bytes(", $be_bytes, "),
    Fix::from_bits(", $bytes_val, ")
);
```
";
                #[inline]
                pub const fn from_be_bytes(bytes: [u8; $nbytes]) -> $Fixed<Frac> {
                    $Fixed::from_bits(<$Inner>::from_be_bytes(bytes))
                }
            }

            comment! {
                "Creates a fixed-point number from its representation
as a byte array in little endian.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(
    Fix::from_le_bytes(", $le_bytes, "),
    Fix::from_bits(", $bytes_val, ")
);
```
";
                #[inline]
                pub const fn from_le_bytes(bytes: [u8; $nbytes]) -> $Fixed<Frac> {
                    $Fixed::from_bits(<$Inner>::from_le_bytes(bytes))
                }
            }

            comment! {
                "Creates a fixed-point number from its representation
as a byte array in native endian.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(
    if cfg!(target_endian = \"big\") {
        Fix::from_ne_bytes(", $be_bytes, ")
    } else {
        Fix::from_ne_bytes(", $le_bytes, ")
    },
    Fix::from_bits(", $bytes_val, ")
);
```
";
                #[inline]
                pub const fn from_ne_bytes(bytes: [u8; $nbytes]) -> $Fixed<Frac> {
                    $Fixed::from_bits(<$Inner>::from_ne_bytes(bytes))
                }
            }

            comment! {
                "Returns the memory representation of this fixed-point
number as a byte array in big-endian byte order.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let val = Fix::from_bits(", $bytes_val, ");
assert_eq!(
    val.to_be_bytes(),
    ", $be_bytes, "
);
```
";
                #[inline]
                pub const fn to_be_bytes(self) -> [u8; $nbytes] {
                    self.to_bits().to_be_bytes()
                }
            }

            comment! {
                "Returns the memory representation of this fixed-point
number as a byte array in little-endian byte order.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let val = Fix::from_bits(", $bytes_val, ");
assert_eq!(
    val.to_le_bytes(),
    ", $le_bytes, "
);
```
";
                #[inline]
                pub const fn to_le_bytes(self) -> [u8; $nbytes] {
                    self.to_bits().to_le_bytes()
                }
            }

            comment! {
                "Returns the memory representation of this fixed-point
number as a byte array in native byte order.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let val = Fix::from_bits(", $bytes_val, ");
assert_eq!(
    val.to_ne_bytes(),
    if cfg!(target_endian = \"big\") {
        ", $be_bytes, "
    } else {
        ", $le_bytes, "
    }
);
```
";
                #[inline]
                pub const fn to_ne_bytes(self) -> [u8; $nbytes] {
                    self.to_bits().to_ne_bytes()
                }
            }

            comment! {
                "Returns the number of ones in the binary
representation.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let f = Fix::from_bits(0b11_0010);
assert_eq!(f.count_ones(), 3);
```
";
                #[inline]
                pub const fn count_ones(self) -> u32 {
                    self.to_bits().count_ones()
                }
            }

            comment! {
                "Returns the number of zeros in the binary
representation.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let f = Fix::from_bits(!0b11_0010);
assert_eq!(f.count_zeros(), 3);
```
";
                #[inline]
                pub const fn count_zeros(self) -> u32 {
                    self.to_bits().count_zeros()
                }
            }

            comment! {
                "Returns the number of leading ones in the binary
representation.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let all_ones = !Fix::from_bits(0);
let f = all_ones - Fix::from_bits(0b10_0000);
assert_eq!(f.leading_ones(), ", $s_nbits, " - 6);
```
";
                #[inline]
                pub const fn leading_ones(self) -> u32 {
                    (!self.to_bits()).leading_zeros()
                }
            }

            comment! {
                "Returns the number of leading zeros in the binary
representation.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let f = Fix::from_bits(0b10_0000);
assert_eq!(f.leading_zeros(), ", $s_nbits, " - 6);
```
";
                #[inline]
                pub const fn leading_zeros(self) -> u32 {
                    self.to_bits().leading_zeros()
                }
            }

            comment! {
                "Returns the number of trailing ones in the binary
representation.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let f = Fix::from_bits(0b101_1111);
assert_eq!(f.trailing_ones(), 5);
```
";
                #[inline]
                pub const fn trailing_ones(self) -> u32 {
                    (!self.to_bits()).trailing_zeros()
                }
            }

            comment! {
                "Returns the number of trailing zeros in the binary
representation.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let f = Fix::from_bits(0b10_0000);
assert_eq!(f.trailing_zeros(), 5);
```
";
                #[inline]
                pub const fn trailing_zeros(self) -> u32 {
                    self.to_bits().trailing_zeros()
                }
            }

            comment! {
                "Reverses the order of the bits of the fixed-point number.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let bits = ", $bytes_val, "_", $s_inner, ";
let rev_bits = bits.reverse_bits();
assert_eq!(Fix::from_bits(bits).reverse_bits(), Fix::from_bits(rev_bits));
```
";
                #[inline]
                pub const fn reverse_bits(self) -> $Fixed<Frac> {
                    $Fixed::from_bits(self.to_bits().reverse_bits())
                }
            }

            comment! {
                "Shifts to the left by `n` bits, wrapping the
truncated bits to the right end.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let bits: ", $s_inner, " = (0b111 << (", $s_nbits, " - 3)) | 0b1010;
let rot = 0b1010111;
assert_eq!(bits.rotate_left(3), rot);
assert_eq!(Fix::from_bits(bits).rotate_left(3), Fix::from_bits(rot));
```
";
                #[inline]
                pub const fn rotate_left(self, n: u32) -> $Fixed<Frac> {
                    Self::from_bits(self.to_bits().rotate_left(n))
                }
            }

            comment! {
                "Shifts to the right by `n` bits, wrapping the
truncated bits to the left end.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let bits: ", $s_inner, " = 0b1010111;
let rot = (0b111 << (", $s_nbits, " - 3)) | 0b1010;
assert_eq!(bits.rotate_right(3), rot);
assert_eq!(Fix::from_bits(bits).rotate_right(3), Fix::from_bits(rot));
```
";
                #[inline]
                pub const fn rotate_right(self, n: u32) -> $Fixed<Frac> {
                    Self::from_bits(self.to_bits().rotate_right(n))
                }
            }

            if_signed! {
                $Signedness;
                comment! {
                    "Returns [`true`] if the number is > 0.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert!(Fix::from_num(5).is_positive());
assert!(!Fix::from_num(0).is_positive());
assert!(!Fix::from_num(-5).is_positive());
```

[`true`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
";
                    #[inline]
                    pub const fn is_positive(self) -> bool {
                        self.to_bits().is_positive()
                    }
                }

                comment! {
                    "Returns [`true`] if the number is < 0.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert!(!Fix::from_num(5).is_negative());
assert!(!Fix::from_num(0).is_negative());
assert!(Fix::from_num(-5).is_negative());
```

[`true`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
";
                    #[inline]
                    pub const fn is_negative(self) -> bool {
                        self.to_bits().is_negative()
                    }
                }
            }

            if_unsigned! {
                $Signedness;
                comment! {
                    "Returns [`true`] if the fixed-point number is
2<sup><i>k</i></sup> for some integer <i>k</i>.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 3/8 is 0.0110
let three_eights = Fix::from_bits(0b0110);
// 1/2 is 0.1000
let half = Fix::from_bits(0b1000);
assert!(!three_eights.is_power_of_two());
assert!(half.is_power_of_two());
```

[`true`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
";
                    #[inline]
                    pub const fn is_power_of_two(self) -> bool {
                        self.to_bits().is_power_of_two()
                    }
                }
            }

            if_true! {
                $HasDouble;
                comment! {
                    "Multiplies two fixed-point numbers and returns a
wider type to retain all precision.

If `self` has <i>i</i> integer bits and <i>f</i> fractional bits, and
`rhs` has <i>j</i> integer bits and <i>g</i> fractional bits, then the
returned fixed-point number will have <i>i</i> + <i>j</i> integer bits
and <i>f</i> + <i>g</i> fractional bits.

# Examples

```rust
use fixed::{
    types::extra::{U2, U4},
    ", $s_fixed, ",
};
// decimal: 1.25 × 1.0625 = 1.328_125
// binary: 1.01 × 1.0001 == 1.010101
let a = ", $s_fixed, "::<U2>::from_num(1.25);
let b = ", $s_fixed, "::<U4>::from_num(1.0625);
assert_eq!(a.wide_mul(b), 1.328_125);
```
";
                    #[inline]
                    pub fn wide_mul<RhsFrac>(
                        self,
                        rhs: $Fixed<RhsFrac>,
                    ) -> $Double<Sum<Frac, RhsFrac>>
                    where
                        Frac: Add<RhsFrac>,
                    {
                        let self_bits = <$DoubleInner>::from(self.to_bits());
                        let rhs_bits = <$DoubleInner>::from(rhs.to_bits());
                        $Double::from_bits(self_bits * rhs_bits)
                    }
                }
            }

            comment! {
                "Multiply and add. Returns `self` × `mul` + `add`.

",
                if_signed_else_empty_str! {
                    $Signedness,
                    "The product `self` × `mul` does not need to be
representable for a valid computation: if the product would overflow
but the final result would not overflow, this method still returns the
correct result.

",
                },
                "The `mul` parameter can have a fixed-point type like
`self` but with a different number of fractional bits.

# Panics

When debug assertions are enabled, this method panics if the result
overflows. When debug assertions are not enabled, the wrapped value
can be returned, but it is not considered a breaking change if in the
future it panics; if wrapping is required use [`wrapping_mul_add`]
instead.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(
    Fix::from_num(4).mul_add(Fix::from_num(0.5), Fix::from_num(3)),
    Fix::from_num(5)
);
",
                if_signed_else_empty_str! {
                    $Signedness,
                    "// MAX × 1.5 − MAX = MAX / 2, which does not overflow
assert_eq!(Fix::MAX.mul_add(Fix::from_num(1.5), -Fix::MAX), Fix::MAX / 2);
"
                },
                "```

[`wrapping_mul_add`]: #method.wrapping_mul_add
";
                #[inline]
                pub fn mul_add<MulFrac: $LeEqU>(
                    self,
                    mul: $Fixed<MulFrac>,
                    add: $Fixed<Frac>,
                ) -> $Fixed<Frac> {
                    let (ans, overflow) = self.to_bits().mul_add_overflow(
                        mul.to_bits(),
                        add.to_bits(),
                        MulFrac::U32,
                    );
                    debug_assert!(!overflow, "overflow");
                    Self::from_bits(ans)
                }
            }

            comment! {
                "Remainder for Euclidean division.

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(7.5).rem_euclid(Fix::from_num(2)), Fix::from_num(1.5));
",
                if_signed_else_empty_str! {
                    $Signedness,
                    "assert_eq!(Fix::from_num(-7.5).rem_euclid(Fix::from_num(2)), Fix::from_num(0.5));
",
                },
                "```
";
                #[inline]
                pub fn rem_euclid(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                    self.checked_rem_euclid(rhs).expect("division by zero")
                }
            }

            if_signed! {
                $Signedness;
                comment! {
                    "Returns the absolute value.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let five = Fix::from_num(5);
let minus_five = Fix::from_num(-5);
assert_eq!(five.abs(), five);
assert_eq!(minus_five.abs(), five);
```
";
                    #[inline]
                    pub const fn abs(self) -> $Fixed<Frac> {
                        Self::from_bits(self.to_bits().abs())
                    }
                }

                comment! {
                    "Returns the absolute value using an unsigned type
without any wrapping or panicking.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, ", ", $s_ufixed, "};
type Fix = ", $s_fixed, "<U4>;
type UFix = ", $s_ufixed, "<U4>;
assert_eq!(Fix::from_num(-5).unsigned_abs(), UFix::from_num(5));
// min_as_unsigned has only highest bit set
let min_as_unsigned = UFix::from_num(1) << (UFix::INT_NBITS - 1);
assert_eq!(Fix::MIN.unsigned_abs(), min_as_unsigned);
```
";
                    #[inline]
                    pub const fn unsigned_abs(self) -> $UFixed<Frac> {
                        $UFixed::from_bits(self.to_bits().wrapping_abs() as $UInner)
                    }
                }
            }

            if_unsigned! {
                $Signedness;
                comment! {
                    "Returns the smallest power of two that is ≥ `self`.

# Panics

When debug assertions are enabled, panics if the next power of two is
too large to represent. When debug assertions are not enabled, zero
can be returned, but it is not considered a breaking change if in the
future it panics; if this is not desirable use
[`checked_next_power_of_two`] instead.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 3/8 is 0.0110
let three_eights = Fix::from_bits(0b0110);
// 1/2 is 0.1000
let half = Fix::from_bits(0b1000);
assert_eq!(three_eights.next_power_of_two(), half);
assert_eq!(half.next_power_of_two(), half);
```

[`checked_next_power_of_two`]: #method.checked_next_power_of_two
";
                    #[inline]
                    pub const fn next_power_of_two(self) -> $Fixed<Frac> {
                        Self::from_bits(self.to_bits().next_power_of_two())
                    }
                }
            }

            comment! {
                "Checked negation. Returns the negated value, or [`None`] on overflow.

",
                if_signed_unsigned! {
                    $Signedness,
                    "Overflow can only occur when negating the minimum value.",
                    "Only zero can be negated without overflow.",
                },
                "

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
",
                if_signed_unsigned! {
                    $Signedness,
                    "assert_eq!(Fix::from_num(5).checked_neg(), Some(Fix::from_num(-5)));
assert_eq!(Fix::MIN.checked_neg(), None);",
                    "assert_eq!(Fix::from_num(0).checked_neg(), Some(Fix::from_num(0)));
assert_eq!(Fix::from_num(5).checked_neg(), None);",
                },
                "
```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
";
                #[inline]
                pub const fn checked_neg(self) -> Option<$Fixed<Frac>> {
                    match self.to_bits().checked_neg() {
                        None => None,
                        Some(bits) => Some(Self::from_bits(bits)),
                    }
                }
            }

            comment! {
                "Checked addition. Returns the sum, or [`None`] on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one = Fix::from_num(1);
assert_eq!((Fix::MAX - one).checked_add(one), Some(Fix::MAX));
assert_eq!(Fix::MAX.checked_add(one), None);
```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
";
                #[inline]
                pub const fn checked_add(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                    match self.to_bits().checked_add(rhs.to_bits()) {
                        None => None,
                        Some(bits) => Some(Self::from_bits(bits)),
                    }
                }
            }

            comment! {
                "Checked subtraction. Returns the difference, or [`None`] on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one = Fix::from_num(1);
assert_eq!((Fix::MIN + one).checked_sub(one), Some(Fix::MIN));
assert_eq!(Fix::MIN.checked_sub(one), None);
```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
";
                #[inline]
                pub const fn checked_sub(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                    match self.to_bits().checked_sub(rhs.to_bits()) {
                        None => None,
                        Some(bits) => Some(Self::from_bits(bits)),
                    }
                }
            }

            comment! {
                "Checked remainder. Returns the remainder, or [`None`] if
the divisor is zero.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(1.5).checked_rem(Fix::from_num(1)), Some(Fix::from_num(0.5)));
assert_eq!(Fix::from_num(1.5).checked_rem(Fix::from_num(0)), None);
```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
";
                #[inline]
                pub fn checked_rem(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                    let rhs_bits = rhs.to_bits();
                    if rhs_bits == 0 {
                        None
                    } else {
                        Some(Self::from_bits(if_signed_unsigned!(
                            $Signedness,
                            if rhs_bits == -1 {
                                0
                            } else {
                                self.to_bits() % rhs_bits
                            },
                            self.to_bits() % rhs_bits,
                        )))
                    }
                }
            }

            comment! {
                "Checked multiply and add.
Returns `self` × `mul` + `add`, or [`None`] on overflow.

",
                if_signed_else_empty_str! {
                    $Signedness,
                    "The product `self` × `mul` does not need to be
representable for a valid computation: if the product would overflow
but the final result would not overflow, this method still returns the
correct result.

",
                },
                "The `mul` parameter can have a fixed-point type like
`self` but with a different number of fractional bits.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(
    Fix::from_num(4).checked_mul_add(Fix::from_num(0.5), Fix::from_num(3)),
    Some(Fix::from_num(5))
);
assert_eq!(Fix::MAX.checked_mul_add(Fix::from_num(1), Fix::from_num(0)), Some(Fix::MAX));
assert_eq!(Fix::MAX.checked_mul_add(Fix::from_num(1), Fix::from_bits(1)), None);
",
                if_signed_else_empty_str! {
                    $Signedness,
                    "// MAX × 1.5 − MAX = MAX / 2, which does not overflow
assert_eq!(Fix::MAX.checked_mul_add(Fix::from_num(1.5), -Fix::MAX), Some(Fix::MAX / 2));
"
                },
                "```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
";
                #[inline]
                pub fn checked_mul_add<MulFrac: $LeEqU>(
                    self,
                    mul: $Fixed<MulFrac>,
                    add: $Fixed<Frac>,
                ) -> Option<$Fixed<Frac>> {
                    match self.to_bits().mul_add_overflow(
                        mul.to_bits(),
                        add.to_bits(),
                        MulFrac::U32,
                    ) {
                        (ans, false) => Some(Self::from_bits(ans)),
                        (_, true) => None,
                    }
                }
            }

            comment! {
                "Checked multiplication by an integer. Returns the
product, or [`None`] on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::MAX.checked_mul_int(1), Some(Fix::MAX));
assert_eq!(Fix::MAX.checked_mul_int(2), None);
```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
";
                #[inline]
                pub const fn checked_mul_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                    match self.to_bits().checked_mul(rhs) {
                        None => None,
                        Some(bits) => Some(Self::from_bits(bits)),
                    }
                }
            }

            comment! {
                "Checked division by an integer. Returns the quotient, or
[`None`] if the divisor is zero",
                if_signed_unsigned! {
                    $Signedness,
                    " or if the division results in overflow.",
                    ".",
                },
                "

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::MAX.checked_div_int(1), Some(Fix::MAX));
assert_eq!(Fix::from_num(1).checked_div_int(0), None);
",
                if_signed_else_empty_str! {
                    $Signedness,
                    "assert_eq!(Fix::MIN.checked_div_int(-1), None);
",
                },
                "```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
";
                #[inline]
                pub fn checked_div_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                    self.to_bits().checked_div(rhs).map(Self::from_bits)
                }
            }

            comment! {
                "Checked remainder for Euclidean division. Returns the
remainder, or [`None`] if the divisor is zero.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let num = Fix::from_num(7.5);
assert_eq!(num.checked_rem_euclid(Fix::from_num(2)), Some(Fix::from_num(1.5)));
assert_eq!(num.checked_rem_euclid(Fix::from_num(0)), None);
",
                if_signed_else_empty_str! {
                    $Signedness,
                    "assert_eq!((-num).checked_rem_euclid(Fix::from_num(2)), Some(Fix::from_num(0.5)));
",
                },
                "```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
";
                #[inline]
                pub fn checked_rem_euclid(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                    let rhs_bits = rhs.to_bits();
                    if rhs_bits == 0 {
                        None
                    } else {
                        Some(Self::from_bits(if_signed_unsigned!(
                            $Signedness,
                            if rhs_bits == -1 {
                                0
                            } else {
                                self.to_bits().rem_euclid(rhs_bits)
                            },
                            self.to_bits() % rhs_bits,
                        )))
                    }
                }
            }

            comment! {
                "Checked shift left. Returns the shifted number,
or [`None`] if `rhs` ≥ ", $s_nbits, ".

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!((Fix::from_num(1) / 2).checked_shl(3), Some(Fix::from_num(4)));
assert_eq!((Fix::from_num(1) / 2).checked_shl(", $s_nbits, "), None);
```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
";
                #[inline]
                pub const fn checked_shl(self, rhs: u32) -> Option<$Fixed<Frac>> {
                    match self.to_bits().checked_shl(rhs) {
                        None => None,
                        Some(bits) => Some(Self::from_bits(bits)),
                    }
                }
            }

            comment! {
                "Checked shift right. Returns the shifted number,
or [`None`] if `rhs` ≥ ", $s_nbits, ".

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(4).checked_shr(3), Some(Fix::from_num(1) / 2));
assert_eq!(Fix::from_num(4).checked_shr(", $s_nbits, "), None);
```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
";
                #[inline]
                pub const fn checked_shr(self, rhs: u32) -> Option<$Fixed<Frac>> {
                    match self.to_bits().checked_shr(rhs) {
                        None => None,
                        Some(bits) => Some(Self::from_bits(bits)),
                    }
                }
            }

            if_signed! {
                $Signedness;
                comment! {
                    "Checked absolute value. Returns the absolute value, or [`None`] on overflow.

Overflow can only occur when trying to find the absolute value of the minimum value.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(-5).checked_abs(), Some(Fix::from_num(5)));
assert_eq!(Fix::MIN.checked_abs(), None);
```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
";
                    #[inline]
                    pub const fn checked_abs(self) -> Option<$Fixed<Frac>> {
                        match self.to_bits().checked_abs() {
                            None => None,
                            Some(bits) => Some(Self::from_bits(bits)),
                        }
                    }
                }
            }

            if_unsigned! {
                $Signedness;
                comment! {
                    "Returns the smallest power of two that is ≥ `self`, or
[`None`] if the next power of two is too large to represent.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 3/8 is 0.0110
let three_eights = Fix::from_bits(0b0110);
// 1/2 is 0.1000
let half = Fix::from_bits(0b1000);
assert_eq!(three_eights.checked_next_power_of_two(), Some(half));
assert!(Fix::MAX.checked_next_power_of_two().is_none());
```

[`None`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.None
";
                    #[inline]
                    pub const fn checked_next_power_of_two(self) -> Option<$Fixed<Frac>> {
                        match self.to_bits().checked_next_power_of_two() {
                            Some(bits) => Some(Self::from_bits(bits)),
                            None => None,
                        }
                    }
                }
            }

            comment! {
                "Saturating negation. Returns the negated value, saturating on overflow.

",
                if_signed_unsigned! {
                    $Signedness,
                    "Overflow can only occur when negating the minimum value.",
                    "This method always returns zero.",
                },
                "

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
",
                if_signed_unsigned! {
                    $Signedness,
                    "assert_eq!(Fix::from_num(5).saturating_neg(), Fix::from_num(-5));
assert_eq!(Fix::MIN.saturating_neg(), Fix::MAX);",
                    "assert_eq!(Fix::from_num(0).saturating_neg(), Fix::from_num(0));
assert_eq!(Fix::from_num(5).saturating_neg(), Fix::from_num(0));",
                },
                "
```
";
                #[inline]
                pub const fn saturating_neg(self) -> $Fixed<Frac> {
                    if_signed_unsigned! {
                        $Signedness,
                        {
                            match self.overflowing_neg() {
                                (val, false) => val,
                                (_, true) => Self::MAX,
                            }
                        },
                        Self::from_bits(0),
                    }
                }
            }

            comment! {
                "Saturating addition. Returns the sum, saturating on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).saturating_add(Fix::from_num(2)), Fix::from_num(5));
assert_eq!(Fix::MAX.saturating_add(Fix::from_num(1)), Fix::MAX);
```
";
                #[inline]
                pub const fn saturating_add(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                    match self.overflowing_add(rhs) {
                        (val, false) => val,
                        (_, true) => if_signed_unsigned! {
                            $Signedness,
                            if self.is_negative() { Self::MIN } else { Self::MAX },
                            Self::MAX,
                        },
                    }
                }
            }

            comment! {
                "Saturating subtraction. Returns the difference, saturating on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
",
                if_signed_unsigned! {
                    $Signedness,
                    "assert_eq!(Fix::from_num(1).saturating_sub(Fix::from_num(3)), Fix::from_num(-2));
assert_eq!(Fix::MIN.saturating_sub(Fix::from_num(1)), Fix::MIN);",
                    "assert_eq!(Fix::from_num(5).saturating_sub(Fix::from_num(3)), Fix::from_num(2));
assert_eq!(Fix::from_num(0).saturating_sub(Fix::from_num(1)), Fix::from_num(0));",
                },
                "
```
";
                #[inline]
                pub const fn saturating_sub(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                    match self.overflowing_sub(rhs) {
                        (val, false) => val,
                        (_, true) => if_signed_unsigned! {
                            $Signedness,
                            if self.to_bits() < rhs.to_bits() {
                                Self::MIN
                            } else {
                                Self::MAX
                            },
                            Self::MIN,
                        },
                    }
                }
            }

            comment! {
                "Saturating multiply and add.
Returns `self` × `mul` + `add`, saturating on overflow.

",
                if_signed_else_empty_str! {
                    $Signedness,
                    "The product `self` × `mul` does not need to be
representable for a valid computation: if the product would overflow
but the final result would not overflow, this method still returns the
correct result.

",
                },
                "The `mul` parameter can have a fixed-point type like
`self` but with a different number of fractional bits.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(
    Fix::from_num(4).saturating_mul_add(Fix::from_num(0.5), Fix::from_num(3)),
    Fix::from_num(5)
);
let half_max = Fix::MAX / 2;
assert_eq!(half_max.saturating_mul_add(Fix::from_num(3), half_max), Fix::MAX);
",
                if_signed_else_empty_str! {
                    $Signedness,
                    "assert_eq!(half_max.saturating_mul_add(Fix::from_num(-5), half_max), Fix::MIN);
// MAX × 1.5 − MAX = MAX / 2, which does not overflow
assert_eq!(Fix::MAX.saturating_mul_add(Fix::from_num(1.5), -Fix::MAX), half_max);
"
                },
                "```
";
                #[inline]
                pub fn saturating_mul_add<MulFrac: $LeEqU>(
                    self,
                    mul: $Fixed<MulFrac>,
                    add: $Fixed<Frac>,
                ) -> $Fixed<Frac> {
                    match self.to_bits().mul_add_overflow(
                        mul.to_bits(),
                        add.to_bits(),
                        MulFrac::U32,
                    ) {
                        (ans, false) => Self::from_bits(ans),
                        (_, true) => {
                            let negative = if_signed_unsigned! {
                                $Signedness,
                                self.is_negative() != mul.is_negative(),
                                false,
                            };
                            if negative {
                                Self::MIN
                            } else {
                                Self::MAX
                            }
                        }
                    }
                }
            }

            comment! {
                "Saturating multiplication by an integer. Returns the product, saturating on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).saturating_mul_int(2), Fix::from_num(6));
assert_eq!(Fix::MAX.saturating_mul_int(2), Fix::MAX);
```
";
                #[inline]
                pub const fn saturating_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
                    match self.overflowing_mul_int(rhs) {
                        (val, false) => val,
                        (_, true) => if_signed_unsigned! {
                            $Signedness,
                            if self.is_negative() != rhs.is_negative() {
                                Self::MIN
                            } else {
                                Self::MAX
                            },
                            Self::MAX,
                        },
                    }
                }
            }

            if_signed! {
                $Signedness;
                comment! {
                    "Saturating absolute value. Returns the absolute value, saturating on overflow.

Overflow can only occur when trying to find the absolute value of the minimum value.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(-5).saturating_abs(), Fix::from_num(5));
assert_eq!(Fix::MIN.saturating_abs(), Fix::MAX);
```
";
                    #[inline]
                    pub const fn saturating_abs(self) -> $Fixed<Frac> {
                        match self.overflowing_abs() {
                            (val, false) => val,
                            (_, true) => Self::MAX,
                        }
                    }
                }
            }

            comment! {
                "Wrapping negation. Returns the negated value, wrapping on overflow.

",
                if_signed_unsigned! {
                    $Signedness,
                    "Overflow can only occur when negating the minimum value.",
                    "Only zero can be negated without overflow.",
                },
                "

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
",
                if_signed_unsigned! {
                    $Signedness,
                    "assert_eq!(Fix::from_num(5).wrapping_neg(), Fix::from_num(-5));
assert_eq!(Fix::MIN.wrapping_neg(), Fix::MIN);",
                    "assert_eq!(Fix::from_num(0).wrapping_neg(), Fix::from_num(0));
assert_eq!(Fix::from_num(5).wrapping_neg(), Fix::wrapping_from_num(-5));
let neg_five_bits = !Fix::from_num(5).to_bits() + 1;
assert_eq!(Fix::from_num(5).wrapping_neg(), Fix::from_bits(neg_five_bits));",
                },
                "
```
";
                #[inline]
                pub const fn wrapping_neg(self) -> $Fixed<Frac> {
                    Self::from_bits(self.to_bits().wrapping_neg())
                }
            }

            comment! {
                "Wrapping addition. Returns the sum, wrapping on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one = Fix::from_num(1);
let one_minus_bit = one - Fix::from_bits(1);
assert_eq!(Fix::from_num(3).wrapping_add(Fix::from_num(2)), Fix::from_num(5));
assert_eq!(Fix::MAX.wrapping_add(one), ",
                if_signed_else_empty_str! { $Signedness, "Fix::MIN + " },
                "one_minus_bit);
```
";
                #[inline]
                pub const fn wrapping_add(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                    Self::from_bits(self.to_bits().wrapping_add(rhs.to_bits()))
                }
            }

            comment! {
                "Wrapping subtraction. Returns the difference, wrapping on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one = Fix::from_num(1);
let one_minus_bit = one - Fix::from_bits(1);
",
                if_signed_unsigned! {
                    $Signedness,
                    "assert_eq!(Fix::from_num(3).wrapping_sub(Fix::from_num(5)), Fix::from_num(-2));
assert_eq!(Fix::MIN",
                    "assert_eq!(Fix::from_num(5).wrapping_sub(Fix::from_num(3)), Fix::from_num(2));
assert_eq!(Fix::from_num(0)",
                },
                ".wrapping_sub(one), Fix::MAX - one_minus_bit);
```
";
                #[inline]
                pub const fn wrapping_sub(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                    Self::from_bits(self.to_bits().wrapping_sub(rhs.to_bits()))
                }
            }

            comment! {
                "Wrapping multiply and add.
Returns `self` × `mul` + `add`, wrapping on overflow.

The `mul` parameter can have a fixed-point type like
`self` but with a different number of fractional bits.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(
    Fix::from_num(4).wrapping_mul_add(Fix::from_num(0.5), Fix::from_num(3)),
    Fix::from_num(5)
);
assert_eq!(Fix::MAX.wrapping_mul_add(Fix::from_num(1), Fix::from_num(0)), Fix::MAX);
assert_eq!(Fix::MAX.wrapping_mul_add(Fix::from_num(1), Fix::from_bits(1)), Fix::MIN);
let wrapped = Fix::MAX.wrapping_mul_int(4);
assert_eq!(Fix::MAX.wrapping_mul_add(Fix::from_num(3), Fix::MAX), wrapped);
```
";
                #[inline]
                pub fn wrapping_mul_add<MulFrac: $LeEqU>(
                    self,
                    mul: $Fixed<MulFrac>,
                    add: $Fixed<Frac>,
                ) -> $Fixed<Frac> {
                    let (ans, _) = self.to_bits().mul_add_overflow(
                        mul.to_bits(),
                        add.to_bits(),
                        MulFrac::U32,
                    );
                    Self::from_bits(ans)
                }
            }

            comment! {
                "Wrapping multiplication by an integer. Returns the product, wrapping on overflow.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).wrapping_mul_int(2), Fix::from_num(6));
let wrapped = Fix::from_bits(!0 << 2);
assert_eq!(Fix::MAX.wrapping_mul_int(4), wrapped);
```
";
                #[inline]
                pub const fn wrapping_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
                    Self::from_bits(self.to_bits().wrapping_mul(rhs))
                }
            }

            comment! {
                "Wrapping division by an integer. Returns the quotient",
                if_signed_unsigned! {
                    $Signedness,
                    ", wrapping on overflow.

Overflow can only occur when dividing the minimum value by −1.",
                    ".

Can never overflow for unsigned values.",
                },
                "

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 1.5 is binary 1.1
let one_point_5 = Fix::from_bits(0b11 << (4 - 1));
assert_eq!(Fix::from_num(3).wrapping_div_int(2), one_point_5);
",
                if_signed_else_empty_str! {
                    $Signedness,
                    "assert_eq!(Fix::MIN.wrapping_div_int(-1), Fix::MIN);
",
                },
                "```
";
                #[inline]
                pub fn wrapping_div_int(self, rhs: $Inner) -> $Fixed<Frac> {
                    Self::from_bits(self.to_bits().wrapping_div(rhs))
                }
            }

            comment! {
                "Wrapping shift left. Wraps `rhs` if `rhs` ≥ ", $s_nbits, ",
then shifts and returns the number.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!((Fix::from_num(1) / 2).wrapping_shl(3), Fix::from_num(4));
assert_eq!((Fix::from_num(1) / 2).wrapping_shl(3 + ", $s_nbits, "), Fix::from_num(4));
```
";
                #[inline]
                pub const fn wrapping_shl(self, rhs: u32) -> $Fixed<Frac> {
                    Self::from_bits(self.to_bits().wrapping_shl(rhs))
                }
            }

            comment! {
                "Wrapping shift right. Wraps `rhs` if `rhs` ≥ ", $s_nbits, ",
then shifts and returns the number.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!((Fix::from_num(4)).wrapping_shr(3), Fix::from_num(1) / 2);
assert_eq!((Fix::from_num(4)).wrapping_shr(3 + ", $s_nbits, "), Fix::from_num(1) / 2);
```
";
                #[inline]
                pub const fn wrapping_shr(self, rhs: u32) -> $Fixed<Frac> {
                    Self::from_bits(self.to_bits().wrapping_shr(rhs))
                }
            }

            if_signed! {
                $Signedness;
                comment! {
                    "Wrapping absolute value. Returns the absolute value, wrapping on overflow.

Overflow can only occur when trying to find the absolute value of the minimum value.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(-5).wrapping_abs(), Fix::from_num(5));
assert_eq!(Fix::MIN.wrapping_abs(), Fix::MIN);
```
";
                    #[inline]
                    pub const fn wrapping_abs(self) -> $Fixed<Frac> {
                        Self::from_bits(self.to_bits().wrapping_abs())
                    }
                }
            }

            if_unsigned! {
                $Signedness;
                comment! {
                    "Returns the smallest power of two that is ≥ `self`,
wrapping to 0 if the next power of two is too large to represent.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 3/8 is 0.0110
let three_eights = Fix::from_bits(0b0110);
// 1/2 is 0.1000
let half = Fix::from_bits(0b1000);
assert_eq!(three_eights.wrapping_next_power_of_two(), half);
assert_eq!(Fix::MAX.wrapping_next_power_of_two(), 0);
```
";
                    #[inline]
                    pub const fn wrapping_next_power_of_two(self) -> $Fixed<Frac> {
                        match self.checked_next_power_of_two() {
                            Some(x) => x,
                            None => Self::from_bits(0),
                        }
                    }
                }
            }

            comment! {
                "Unwrapped negation. Returns the negated value, panicking on overflow.

",
                if_signed_unsigned! {
                    $Signedness,
                    "Overflow can only occur when negating the minimum value.",
                    "Only zero can be negated without overflow.",
                },
                "

# Panics

Panics if the result does not fit.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
",
                if_signed_unsigned! {
                    $Signedness,
                    concat!(
                        "assert_eq!(Fix::from_num(5).unwrapped_neg(), Fix::from_num(-5));
```

The following panics because of overflow.

```should_panic
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let _overflow = Fix::MIN.unwrapped_neg();",
                    ),
                    concat!(
                        "assert_eq!(Fix::from_num(0).unwrapped_neg(), Fix::from_num(0));
```

The following panics because of overflow.

```should_panic
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let _overflow = Fix::from_num(5).unwrapped_neg();",
                    ),
                },
                "
```
";
                #[inline]
                pub fn unwrapped_neg(self) -> $Fixed<Frac> {
                    self.checked_neg().expect("overflow")
                }
            }

            comment! {
                "Unwrapped addition. Returns the sum, panicking on overflow.

# Panics

Panics if the result does not fit.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).unwrapped_add(Fix::from_num(2)), Fix::from_num(5));
```

The following panics because of overflow.

```should_panic
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let _overflow = Fix::MAX.unwrapped_add(Fix::from_bits(1));
```
";
                #[inline]
                pub fn unwrapped_add(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                    self.checked_add(rhs).expect("overflow")
                }
            }

            comment! {
                "Unwrapped subtraction. Returns the difference, panicking on overflow.

# Panics

Panics if the result does not fit.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
",
                if_signed_unsigned! {
                    $Signedness,
                    "assert_eq!(Fix::from_num(3).unwrapped_sub(Fix::from_num(5)), Fix::from_num(-2));
",
                    "assert_eq!(Fix::from_num(5).unwrapped_sub(Fix::from_num(3)), Fix::from_num(2));
",
                },
                "```

The following panics because of overflow.

```should_panic
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let _overflow = Fix::MIN.unwrapped_sub(Fix::from_bits(1));
```
";
                #[inline]
                pub fn unwrapped_sub(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                    self.checked_sub(rhs).expect("overflow")
                }
            }

            comment! {
                "Unwrapped multiply and add.
Returns `self` × `mul` + `add`, panicking on overflow.

",
                if_signed_else_empty_str! {
                    $Signedness,
                    "The product `self` × `mul` does not need to be
representable for a valid computation: if the product would overflow
but the final result would not overflow, this method still returns the
correct result.

",
                },
                "The `mul` parameter can have a fixed-point type like
`self` but with a different number of fractional bits.

# Panics

Panics if the result does not fit.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(
    Fix::from_num(4).unwrapped_mul_add(Fix::from_num(0.5), Fix::from_num(3)),
    Fix::from_num(5)
);
",
                if_signed_else_empty_str! {
                    $Signedness,
                    "// MAX × 1.5 − MAX = MAX / 2, which does not overflow
assert_eq!(Fix::MAX.unwrapped_mul_add(Fix::from_num(1.5), -Fix::MAX), Fix::MAX / 2);
"
                },
                "```

The following panics because of overflow.

```should_panic
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let _overflow = Fix::MAX.unwrapped_mul_add(Fix::from_num(1), Fix::from_bits(1));
```
";
                #[inline]
                pub fn unwrapped_mul_add<MulFrac: $LeEqU>(
                    self,
                    mul: $Fixed<MulFrac>,
                    add: $Fixed<Frac>,
                ) -> $Fixed<Frac> {
                    self.checked_mul_add(mul, add).expect("overflow")
                }
            }

            comment! {
                "Unwrapped multiplication by an integer. Returns the product, panicking on overflow.

# Panics

Panics if the result does not fit.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).unwrapped_mul_int(2), Fix::from_num(6));
```

The following panics because of overflow.

```should_panic
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let _overflow = Fix::MAX.unwrapped_mul_int(4);
```
";
                #[inline]
                pub fn unwrapped_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
                    self.checked_mul_int(rhs).expect("overflow")
                }
            }

            comment! {
                "Unwrapped division by an integer. Returns the quotient",
                if_signed_unsigned! {
                    $Signedness,
                    ", panicking on overflow.

Overflow can only occur when dividing the minimum value by −1.",
                    ".

Can never overflow for unsigned values.",
                },
                "

# Panics

Panics if the divisor is zero",
                if_signed_else_empty_str! {
                    $Signedness,
                    " or if the division results in overflow",
                },
                ".

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 1.5 is binary 1.1
let one_point_5 = Fix::from_bits(0b11 << (4 - 1));
assert_eq!(Fix::from_num(3).unwrapped_div_int(2), one_point_5);
",
                if_signed_else_empty_str! {
                    $Signedness,
                    "```

The following panics because of overflow.

```should_panic
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let _overflow = Fix::MIN.unwrapped_div_int(-1);
",
                },
                "```
";
                #[inline]
                pub fn unwrapped_div_int(self, rhs: $Inner) -> $Fixed<Frac> {
                    match self.overflowing_div_int(rhs) {
                        (_, true) => panic!("overflow"),
                        (ans, false) => ans,
                    }
                }
            }

            comment! {
                "Unwrapped shift left. Panics if `rhs` ≥ ", $s_nbits, ".

# Panics

Panics if `rhs` ≥ ", $s_nbits, ".

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!((Fix::from_num(1) / 2).unwrapped_shl(3), Fix::from_num(4));
```

The following panics because of overflow.

```should_panic
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let _overflow = Fix::from_num(1).unwrapped_shl(", $s_nbits, ");
```
";
                #[inline]
                pub fn unwrapped_shl(self, rhs: u32) -> $Fixed<Frac> {
                    self.checked_shl(rhs).expect("overflow")
                }
            }

            comment! {
                "Unwrapped shift right. Panics if `rhs` ≥ ", $s_nbits, ".

# Panics

Panics if `rhs` ≥ ", $s_nbits, ".

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!((Fix::from_num(4)).unwrapped_shr(3), Fix::from_num(1) / 2);
```

The following panics because of overflow.

```should_panic
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let _overflow = Fix::from_num(1).unwrapped_shr(", $s_nbits, ");
```
";
                #[inline]
                pub fn unwrapped_shr(self, rhs: u32) -> $Fixed<Frac> {
                    self.checked_shr(rhs).expect("overflow")
                }
            }

            if_signed! {
                $Signedness;
                comment! {
                    "Unwrapped absolute value. Returns the absolute value, panicking on overflow.

Overflow can only occur when trying to find the absolute value of the minimum value.

# Panics

Panics if the result does not fit.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(-5).unwrapped_abs(), Fix::from_num(5));
```

The following panics because of overflow.

```should_panic
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let _overflow = Fix::MIN.unwrapped_abs();
```
";
                    #[inline]
                    pub fn unwrapped_abs(self) -> $Fixed<Frac> {
                        self.checked_abs().expect("overflow")
                    }
                }
            }

            if_unsigned! {
                $Signedness;
                comment! {
                    "Returns the smallest power of two that is ≥ `self`,
panicking if the next power of two is too large to represent.

# Panics

Panics if the result does not fit.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 3/8 is 0.0110
let three_eights = Fix::from_bits(0b0110);
// 1/2 is 0.1000
let half = Fix::from_bits(0b1000);
assert_eq!(three_eights.unwrapped_next_power_of_two(), half);
```

The following panics because of overflow.

```should_panic
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let _overflow = Fix::MAX.unwrapped_next_power_of_two();
```
";
                    #[inline]
                    pub fn unwrapped_next_power_of_two(self) -> $Fixed<Frac> {
                        self.checked_next_power_of_two().expect("overflow")
                    }
                }
            }

            comment! {
                "Overflowing negation.

Returns a [tuple] of the negated value and a [`bool`] indicating whether
an overflow has occurred. On overflow, the wrapped value is returned.

",
                if_signed_unsigned! {
                    $Signedness,
                    "Overflow can only occur when negating the minimum value.",
                    "Only zero can be negated without overflow.",
                },
                "

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
",
                if_signed_unsigned! {
                    $Signedness,
                    "assert_eq!(Fix::from_num(5).overflowing_neg(), (Fix::from_num(-5), false));
assert_eq!(Fix::MIN.overflowing_neg(), (Fix::MIN, true));",
                    "assert_eq!(Fix::from_num(0).overflowing_neg(), (Fix::from_num(0), false));
assert_eq!(Fix::from_num(5).overflowing_neg(), Fix::overflowing_from_num(-5));
let neg_five_bits = !Fix::from_num(5).to_bits() + 1;
assert_eq!(Fix::from_num(5).overflowing_neg(), (Fix::from_bits(neg_five_bits), true));",
                },
                "
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
                #[inline]
                pub const fn overflowing_neg(self) -> ($Fixed<Frac>, bool) {
                    let (ans, o) = self.to_bits().overflowing_neg();
                    (Self::from_bits(ans), o)
                }
            }

            comment! {
                "Overflowing addition.

Returns a [tuple] of the sum and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one = Fix::from_num(1);
let one_minus_bit = one - Fix::from_bits(1);
assert_eq!(Fix::from_num(3).overflowing_add(Fix::from_num(2)), (Fix::from_num(5), false));
assert_eq!(Fix::MAX.overflowing_add(one), (",
                if_signed_else_empty_str! { $Signedness, "Fix::MIN + " },
                "one_minus_bit, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
                #[inline]
                pub const fn overflowing_add(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                    let (ans, o) = self.to_bits().overflowing_add(rhs.to_bits());
                    (Self::from_bits(ans), o)
                }
            }

            comment! {
                "Overflowing subtraction.

Returns a [tuple] of the difference and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
let one = Fix::from_num(1);
let one_minus_bit = one - Fix::from_bits(1);
",
                if_signed_unsigned! {
                    $Signedness,
                    "assert_eq!(Fix::from_num(3).overflowing_sub(Fix::from_num(5)), (Fix::from_num(-2), false));
assert_eq!(Fix::MIN",
                    "assert_eq!(Fix::from_num(5).overflowing_sub(Fix::from_num(3)), (Fix::from_num(2), false));
assert_eq!(Fix::from_num(0)",
                },
                ".overflowing_sub(one), (Fix::MAX - one_minus_bit, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
                #[inline]
                pub const fn overflowing_sub(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                    let (ans, o) = self.to_bits().overflowing_sub(rhs.to_bits());
                    (Self::from_bits(ans), o)
                }
            }

            comment! {
                "Overflowing multiply and add.

Returns a [tuple] of `self` × `mul` + `add` and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

The `mul` parameter can have a fixed-point type like
`self` but with a different number of fractional bits.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(
    Fix::MAX.overflowing_mul_add(Fix::from_num(1), Fix::from_num(0)),
    (Fix::MAX, false)
);
assert_eq!(
    Fix::MAX.overflowing_mul_add(Fix::from_num(1), Fix::from_bits(1)),
    (Fix::MIN, true)
);
assert_eq!(
    Fix::MAX.overflowing_mul_add(Fix::from_num(3), Fix::MAX),
    Fix::MAX.overflowing_mul_int(4)
);
",
                if_signed_else_empty_str! {
                    $Signedness,
                    "// MAX × 1.5 − MAX = MAX / 2, which does not overflow
assert_eq!(
    Fix::MAX.overflowing_mul_add(Fix::from_num(1.5), -Fix::MAX),
    (Fix::MAX / 2, false)
);
"
                },
                "```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
                #[inline]
                pub fn overflowing_mul_add<MulFrac: $LeEqU>(
                    self,
                    mul: $Fixed<MulFrac>,
                    add: $Fixed<Frac>,
                ) -> ($Fixed<Frac>, bool) {
                    let (ans, overflow) = self.to_bits().mul_add_overflow(
                        mul.to_bits(),
                        add.to_bits(),
                        MulFrac::U32,
                    );
                    (Self::from_bits(ans), overflow)
                }
            }

            comment! {
                "Overflowing multiplication by an integer.

Returns a [tuple] of the product and a [`bool`] indicating whether an
overflow has occurred. On overflow, the wrapped value is returned.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(3).overflowing_mul_int(2), (Fix::from_num(6), false));
let wrapped = Fix::from_bits(!0 << 2);
assert_eq!(Fix::MAX.overflowing_mul_int(4), (wrapped, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
                #[inline]
                pub const fn overflowing_mul_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                    let (ans, o) = self.to_bits().overflowing_mul(rhs);
                    (Self::from_bits(ans), o)
                }
            }

            comment! {
                "Overflowing division by an integer.

Returns a [tuple] of the quotient and ",
                if_signed_unsigned! {
                    $Signedness,
                    "a [`bool`] indicating whether an overflow has
occurred. On overflow, the wrapped value is returned. Overflow can
only occur when dividing the minimum value by −1.",
                    "[`false`], as the division can never overflow for unsigned values.",
                },
                "

# Panics

Panics if the divisor is zero.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
// 1.5 is binary 1.1
let one_point_5 = Fix::from_bits(0b11 << (4 - 1));
assert_eq!(Fix::from_num(3).overflowing_div_int(2), (one_point_5, false));
",
                if_signed_else_empty_str! {
                    $Signedness,
                    "assert_eq!(Fix::MIN.overflowing_div_int(-1), (Fix::MIN, true));
",
                },
                "```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[`false`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
                #[inline]
                pub fn overflowing_div_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                    let (ans, o) = self.to_bits().overflowing_div(rhs);
                    (Self::from_bits(ans), o)
                }
            }

            comment! {
                "Overflowing shift left.

Returns a [tuple] of the shifted value and a [`bool`] indicating whether
an overflow has occurred. Overflow occurs when `rhs` ≥ ", $s_nbits, ".
On overflow `rhs` is wrapped before the shift operation.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!((Fix::from_num(1) / 2).overflowing_shl(3), (Fix::from_num(4), false));
assert_eq!((Fix::from_num(1) / 2).overflowing_shl(3 + ", $s_nbits, "), (Fix::from_num(4), true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
                #[inline]
                pub const fn overflowing_shl(self, rhs: u32) -> ($Fixed<Frac>, bool) {
                    let (ans, o) = self.to_bits().overflowing_shl(rhs);
                    (Self::from_bits(ans), o)
                }
            }

            comment! {
                "Overflowing shift right.

Returns a [tuple] of the shifted value and a [`bool`] indicating whether
an overflow has occurred. Overflow occurs when `rhs` ≥ ", $s_nbits, ".
On overflow `rhs` is wrapped before the shift operation.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!((Fix::from_num(4)).overflowing_shr(3), (Fix::from_num(1) / 2, false));
assert_eq!((Fix::from_num(4)).overflowing_shr(3 + ", $s_nbits, "), (Fix::from_num(1) / 2, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
                #[inline]
                pub const fn overflowing_shr(self, rhs: u32) -> ($Fixed<Frac>, bool) {
                    let (ans, o) = self.to_bits().overflowing_shr(rhs);
                    (Self::from_bits(ans), o)
                }
            }

            if_signed! {
                $Signedness;
                comment! {
                    "Overflowing absolute value.

Returns a [tuple] of the absolute value and a [`bool`] indicating
whether an overflow has occurred. On overflow, the wrapped value is
returned.

Overflow can only occur when trying to find the absolute value of the minimum value.

# Examples

```rust
use fixed::{types::extra::U4, ", $s_fixed, "};
type Fix = ", $s_fixed, "<U4>;
assert_eq!(Fix::from_num(-5).overflowing_abs(), (Fix::from_num(5), false));
assert_eq!(Fix::MIN.overflowing_abs(), (Fix::MIN, true));
```

[`bool`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
[tuple]: https://doc.rust-lang.org/nightly/std/primitive.tuple.html
";
                    #[inline]
                    pub const fn overflowing_abs(self) -> ($Fixed<Frac>, bool) {
                        let (ans, o) = self.to_bits().overflowing_abs();
                        (Self::from_bits(ans), o)
                    }
                }
            }
        }
    };
}
