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

use crate::{
    from_str::ParseFixedError,
    traits::{Fixed, FixedSigned, FixedUnsigned, FromFixed, ToFixed},
    types::extra::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    fmt::{Display, Formatter, Result as FmtResult},
    iter::{Product, Sum},
    mem,
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
    str::FromStr,
};

/// Provides arithmetic operations that panic on overflow even when
/// debug assertions are disabled.
///
/// The underlying value can be retrieved through the `.0` index.
///
/// # Examples
///
/// This panics even when debug assertions are disabled.
///
/// ```should_panic
/// use fixed::{types::I16F16, Unwrapped};
/// let max = Unwrapped(I16F16::MAX);
/// let delta = Unwrapped(I16F16::from_bits(1));
/// let _overflow = max + delta;
/// ```
#[repr(transparent)]
#[derive(Clone, Copy, Default, Hash, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Unwrapped<F>(pub F);

impl<F: Fixed> Unwrapped<F> {
    /// The smallest value that can be represented.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert_eq!(Unwrapped::<I16F16>::MIN, Unwrapped(I16F16::MIN));
    /// ```
    pub const MIN: Unwrapped<F> = Unwrapped(F::MIN);

    /// The largest value that can be represented.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert_eq!(Unwrapped::<I16F16>::MAX, Unwrapped(I16F16::MAX));
    /// ```
    pub const MAX: Unwrapped<F> = Unwrapped(F::MAX);

    /// The number of integer bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert_eq!(Unwrapped::<I16F16>::INT_NBITS, I16F16::INT_NBITS);
    /// ```
    pub const INT_NBITS: u32 = F::INT_NBITS;

    /// The number of fractional bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert_eq!(Unwrapped::<I16F16>::FRAC_NBITS, I16F16::FRAC_NBITS);
    /// ```
    pub const FRAC_NBITS: u32 = F::FRAC_NBITS;

    /// Creates a fixed-point number that has a bitwise representation
    /// identical to the given integer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert_eq!(Unwrapped::<I16F16>::from_bits(0x1C), Unwrapped(I16F16::from_bits(0x1C)));
    /// ```
    #[inline]
    pub fn from_bits(bits: F::Bits) -> Unwrapped<F> {
        Unwrapped(F::from_bits(bits))
    }

    /// Creates an integer that has a bitwise representation identical
    /// to the given fixed-point number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let w = Unwrapped(I16F16::from_bits(0x1C));
    /// assert_eq!(w.to_bits(), 0x1C);
    /// ```
    #[inline]
    pub fn to_bits(self) -> F::Bits {
        self.0.to_bits()
    }

    /// Converts a fixed-point number from big endian to the target’s
    /// endianness.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let w = Unwrapped(I16F16::from_bits(0x1234_5678));
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(Unwrapped::from_be(w), w);
    /// } else {
    ///     assert_eq!(Unwrapped::from_be(w), w.swap_bytes());
    /// }
    /// ```
    #[inline]
    pub fn from_be(w: Self) -> Self {
        Unwrapped(F::from_be(w.0))
    }

    /// Converts a fixed-point number from little endian to the
    /// target’s endianness.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let w = Unwrapped(I16F16::from_bits(0x1234_5678));
    /// if cfg!(target_endian = "little") {
    ///     assert_eq!(Unwrapped::from_le(w), w);
    /// } else {
    ///     assert_eq!(Unwrapped::from_le(w), w.swap_bytes());
    /// }
    /// ```
    #[inline]
    pub fn from_le(w: Self) -> Self {
        Unwrapped(F::from_le(w.0))
    }

    /// Converts `self` to big endian from the target’s endianness.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let w = Unwrapped(I16F16::from_bits(0x1234_5678));
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(w.to_be(), w);
    /// } else {
    ///     assert_eq!(w.to_be(), w.swap_bytes());
    /// }
    /// ```
    #[inline]
    pub fn to_be(self) -> Self {
        Unwrapped(self.0.to_be())
    }

    /// Converts `self` to little endian from the target’s endianness.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let w = Unwrapped(I16F16::from_bits(0x1234_5678));
    /// if cfg!(target_endian = "little") {
    ///     assert_eq!(w.to_le(), w);
    /// } else {
    ///     assert_eq!(w.to_le(), w.swap_bytes());
    /// }
    /// ```
    #[inline]
    pub fn to_le(self) -> Self {
        Unwrapped(self.0.to_le())
    }

    /// Reverses the byte order of the fixed-point number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let w = Unwrapped(I16F16::from_bits(0x1234_5678));
    /// let swapped = Unwrapped(I16F16::from_bits(0x7856_3412));
    /// assert_eq!(w.swap_bytes(), swapped);
    /// ```
    #[inline]
    pub fn swap_bytes(self) -> Self {
        Unwrapped(self.0.swap_bytes())
    }

    /// Creates a fixed-point number from its representation
    /// as a byte array in big endian.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let bytes = [0x12, 0x34, 0x56, 0x78];
    /// assert_eq!(
    ///     Unwrapped::<I16F16>::from_be_bytes(bytes),
    ///     Unwrapped::<I16F16>::from_bits(0x1234_5678)
    /// );
    /// ```
    #[inline]
    pub fn from_be_bytes(bytes: F::Bytes) -> Self {
        Unwrapped(F::from_be_bytes(bytes))
    }

    /// Creates a fixed-point number from its representation
    /// as a byte array in little endian.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let bytes = [0x78, 0x56, 0x34, 0x12];
    /// assert_eq!(
    ///     Unwrapped::<I16F16>::from_le_bytes(bytes),
    ///     Unwrapped::<I16F16>::from_bits(0x1234_5678)
    /// );
    /// ```
    #[inline]
    pub fn from_le_bytes(bytes: F::Bytes) -> Self {
        Unwrapped(F::from_le_bytes(bytes))
    }

    /// Creates a fixed-point number from its representation
    /// as a byte array in native endian.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let bytes = if cfg!(target_endian = "big") {
    ///     [0x12, 0x34, 0x56, 0x78]
    /// } else {
    ///     [0x78, 0x56, 0x34, 0x12]
    /// };
    /// assert_eq!(
    ///     Unwrapped::<I16F16>::from_ne_bytes(bytes),
    ///     Unwrapped::<I16F16>::from_bits(0x1234_5678)
    /// );
    /// ```
    #[inline]
    pub fn from_ne_bytes(bytes: F::Bytes) -> Self {
        Unwrapped(F::from_ne_bytes(bytes))
    }

    /// Returns the memory representation of this fixed-point
    /// number as a byte array in big-endian byte order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert_eq!(
    ///     Unwrapped::<I16F16>::from_bits(0x1234_5678).to_be_bytes(),
    ///     [0x12, 0x34, 0x56, 0x78]
    /// );
    /// ```
    #[inline]
    pub fn to_be_bytes(self) -> F::Bytes {
        self.0.to_be_bytes()
    }

    /// Returns the memory representation of this fixed-point
    /// number as a byte array in little-endian byte order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert_eq!(
    ///     Unwrapped::<I16F16>::from_bits(0x1234_5678).to_le_bytes(),
    ///     [0x78, 0x56, 0x34, 0x12]
    /// );
    /// ```
    #[inline]
    pub fn to_le_bytes(self) -> F::Bytes {
        self.0.to_le_bytes()
    }

    /// Returns the memory representation of this fixed-point
    /// number as a byte array in native-endian byte order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let bytes = if cfg!(target_endian = "big") {
    ///     [0x12, 0x34, 0x56, 0x78]
    /// } else {
    ///     [0x78, 0x56, 0x34, 0x12]
    /// };
    /// assert_eq!(
    ///     Unwrapped::<I16F16>::from_bits(0x1234_5678).to_ne_bytes(),
    ///     bytes
    /// );
    /// ```
    #[inline]
    pub fn to_ne_bytes(self) -> F::Bytes {
        self.0.to_ne_bytes()
    }

    /// Unwrapped conversion from another number.
    ///
    /// The other number can be:
    ///
    ///   * A fixed-point number. Any extra fractional bits are
    ///     discarded, which rounds towards −∞.
    ///   * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    ///     [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    ///     [`usize`].
    ///   * A floating-point number of type [`f32`] or [`f64`]. If the
    ///     [`f16` feature] is enabled, it can also be of type [`f16`]
    ///     or [`bf16`]. For this conversion, the method rounds to the
    ///     nearest, with ties rounding to even.
    ///   * Any other number `src` for which [`ToFixed`] is implemented.
    ///
    /// # Panics
    ///
    /// Panics if the value does not fit.
    ///
    /// For floating-point numbers, also panics if the value is not [finite].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{
    ///     types::{I4F4, I16F16},
    ///     Unwrapped,
    /// };
    /// let src = I16F16::from_num(1.75);
    /// let dst = Unwrapped::<I4F4>::from_num(src);
    /// assert_eq!(dst, Unwrapped(I4F4::from_num(1.75)));
    /// ```
    ///
    /// The following panics even when debug assertions are disabled.
    ///
    /// ```should_panic
    /// use fixed::{
    ///     types::{I4F4, I16F16},
    ///     Unwrapped,
    /// };
    /// let src = I16F16::from_bits(0x1234_5678);
    /// let _overflow = Unwrapped::<I4F4>::from_num(src);
    /// ```
    ///
    /// [`ToFixed`]: traits/trait.ToFixed.html
    /// [`Unwrapped`]: struct.Unwrapped.html
    /// [`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
    /// [`f16` feature]: index.html#optional-features
    /// [`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
    /// [`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
    /// [`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
    /// [`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
    /// [`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
    /// [`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
    /// [`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
    /// [`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
    /// [`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
    /// [`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
    /// [`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
    /// [`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
    /// [`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
    /// [`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
    /// [`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
    /// [finite]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
    #[inline]
    pub fn from_num<Src: ToFixed>(src: Src) -> Unwrapped<F> {
        match src.overflowing_to_fixed() {
            (_, true) => panic!("overflow"),
            (ans, false) => Unwrapped(ans),
        }
    }

    /// Converts a fixed-point number to another number, panicking on
    /// overflow.
    ///
    /// The other number can be:
    ///
    ///   * Another fixed-point number. Any extra fractional bits are
    ///     discarded, which rounds towards −∞.
    ///   * An integer of type [`i8`], [`i16`], [`i32`], [`i64`], [`i128`],
    ///     [`isize`], [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or
    ///     [`usize`]. Any fractional bits are discarded, which rounds
    ///     towards −∞.
    ///   * A floating-point number of type [`f32`] or [`f64`]. If the
    ///     [`f16` feature] is enabled, it can also be of type [`f16`]
    ///     or [`bf16`]. For this conversion, the method rounds to the
    ///     nearest, with ties rounding to even.
    ///   * Any other type `Dst` for which [`FromFixed`] is implemented.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{
    ///     types::{I16F16, I4F4},
    ///     Unwrapped,
    /// };
    /// let src = Unwrapped(I4F4::from_num(1.75));
    /// assert_eq!(src.to_num::<I16F16>(), I16F16::from_num(1.75));
    /// ```
    ///
    /// The following panics even when debug assertions are disabled.
    ///
    /// ```should_panic
    /// use fixed::{
    ///     types::{I2F6, I4F4},
    ///     Unwrapped,
    /// };
    /// let src = Unwrapped(I4F4::MAX);
    /// let _overflow = src.to_num::<I2F6>();
    /// ```
    ///
    /// [`FromFixed`]: traits/trait.FromFixed.html
    /// [`bf16`]: https://docs.rs/half/^1.2/half/struct.bf16.html
    /// [`f16` feature]: index.html#optional-features
    /// [`f16`]: https://docs.rs/half/^1.2/half/struct.f16.html
    /// [`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
    /// [`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
    /// [`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
    /// [`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
    /// [`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
    /// [`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
    /// [`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
    /// [`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
    /// [`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
    /// [`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
    /// [`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
    /// [`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
    /// [`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
    /// [`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
    #[inline]
    pub fn to_num<Dst: FromFixed>(self) -> Dst {
        match Dst::overflowing_from_fixed(self.0) {
            (_, true) => panic!("overflow"),
            (ans, false) => ans,
        }
    }

    /// Parses a string slice containing binary digits to return a fixed-point number.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I8F8, Unwrapped};
    /// let check = Unwrapped(I8F8::from_bits(0b1110001 << (8 - 1)));
    /// assert_eq!(Unwrapped::<I8F8>::from_str_binary("111000.1"), Ok(check));
    /// ```
    #[inline]
    pub fn from_str_binary(src: &str) -> Result<Unwrapped<F>, ParseFixedError> {
        F::from_str_binary(src).map(Unwrapped)
    }

    /// Parses a string slice containing octal digits to return a fixed-point number.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I8F8, Unwrapped};
    /// let check = Unwrapped(I8F8::from_bits(0o1654 << (8 - 3)));
    /// assert_eq!(Unwrapped::<I8F8>::from_str_octal("165.4"), Ok(check));
    /// ```
    #[inline]
    pub fn from_str_octal(src: &str) -> Result<Unwrapped<F>, ParseFixedError> {
        F::from_str_octal(src).map(Unwrapped)
    }

    /// Parses a string slice containing hexadecimal digits to return a fixed-point number.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I8F8, Unwrapped};
    /// let check = Unwrapped(I8F8::from_bits(0xFFE));
    /// assert_eq!(Unwrapped::<I8F8>::from_str_hex("F.FE"), Ok(check));
    /// ```
    #[inline]
    pub fn from_str_hex(src: &str) -> Result<Unwrapped<F>, ParseFixedError> {
        F::from_str_hex(src).map(Unwrapped)
    }

    /// Returns the integer part.
    ///
    /// Note that since the numbers are stored in two’s complement,
    /// negative numbers with non-zero fractional parts will be
    /// rounded towards −∞, except in the case where there are no
    /// integer bits, for example for the type
    /// <code>[Unwrapped][`Unwrapped`]&lt;[I0F16][`I0F16`]&gt;</code>,
    /// where the return value is always zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert_eq!(Unwrapped(I16F16::from_num(12.25)).int(), Unwrapped(I16F16::from_num(12)));
    /// assert_eq!(Unwrapped(I16F16::from_num(-12.25)).int(), Unwrapped(I16F16::from_num(-13)));
    /// ```
    ///
    /// [`I0F16`]: types/type.I0F16.html
    /// [`Unwrapped`]: struct.Unwrapped.html
    #[inline]
    pub fn int(self) -> Unwrapped<F> {
        Unwrapped(self.0.int())
    }

    /// Returns the fractional part.
    ///
    /// Note that since the numbers are stored in two’s complement,
    /// the returned fraction will be non-negative for negative
    /// numbers, except in the case where there are no integer bits,
    /// for example for the type
    /// <code>[Unwrapped][`Unwrapped`]&lt;[I0F16][`I0F16`]&gt;</code>,
    /// where the return value is always equal to `self`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert_eq!(Unwrapped(I16F16::from_num(12.25)).frac(), Unwrapped(I16F16::from_num(0.25)));
    /// assert_eq!(Unwrapped(I16F16::from_num(-12.25)).frac(), Unwrapped(I16F16::from_num(0.75)));
    /// ```
    ///
    /// [`I0F16`]: types/type.I0F16.html
    /// [`Unwrapped`]: struct.Unwrapped.html
    #[inline]
    pub fn frac(self) -> Unwrapped<F> {
        Unwrapped(self.0.frac())
    }

    /// Rounds to the next integer towards 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let three = Unwrapped(I16F16::from_num(3));
    /// assert_eq!(Unwrapped(I16F16::from_num(3.9)).round_to_zero(), three);
    /// assert_eq!(Unwrapped(I16F16::from_num(-3.9)).round_to_zero(), -three);
    /// ```
    #[inline]
    pub fn round_to_zero(self) -> Unwrapped<F> {
        Unwrapped(self.0.round_to_zero())
    }

    /// Unwrapped ceil. Rounds to the next integer towards +∞, panicking
    /// on overflow.
    ///
    /// # Panics
    ///
    /// Panics if the result does not fit.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let two_half = Unwrapped(I16F16::from_num(5) / 2);
    /// assert_eq!(two_half.ceil(), Unwrapped(I16F16::from_num(3)));
    /// ```
    ///
    /// The following panics because of overflow.
    ///
    /// ```should_panic
    /// use fixed::{types::I16F16, Unwrapped};
    /// let _overflow = Unwrapped(I16F16::MAX).ceil();
    /// ```
    #[inline]
    pub fn ceil(self) -> Unwrapped<F> {
        Unwrapped(self.0.unwrapped_ceil())
    }

    /// Unwrapped floor. Rounds to the next integer towards −∞,
    /// panicking on overflow.
    ///
    /// Overflow can only occur for signed numbers with zero integer
    /// bits.
    ///
    /// # Panics
    ///
    /// Panics if the result does not fit.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let two_half = Unwrapped(I16F16::from_num(5) / 2);
    /// assert_eq!(two_half.floor(), Unwrapped(I16F16::from_num(2)));
    /// ```
    ///
    /// The following panics because of overflow.
    ///
    /// ```should_panic
    /// use fixed::{types::I0F32, Unwrapped};
    /// let _overflow = Unwrapped(I0F32::MIN).floor();
    /// ```
    #[inline]
    pub fn floor(self) -> Unwrapped<F> {
        Unwrapped(self.0.unwrapped_floor())
    }

    /// Unwrapped round. Rounds to the next integer to the nearest,
    /// with ties rounded away from zero, and panics on overflow.
    ///
    /// # Panics
    ///
    /// Panics if the result does not fit.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let two_half = Unwrapped(I16F16::from_num(5) / 2);
    /// assert_eq!(two_half.round(), Unwrapped(I16F16::from_num(3)));
    /// assert_eq!((-two_half).round(), Unwrapped(I16F16::from_num(-3)));
    /// ```
    ///
    /// The following panics because of overflow.
    ///
    /// ```should_panic
    /// use fixed::{types::I16F16, Unwrapped};
    /// let _overflow = Unwrapped(I16F16::MAX).round();
    /// ```
    #[inline]
    pub fn round(self) -> Unwrapped<F> {
        Unwrapped(self.0.unwrapped_round())
    }

    /// Unwrapped round. Rounds to the next integer to the nearest,
    /// with ties rounded to even, and panics on overflow.
    ///
    /// # Panics
    ///
    /// Panics if the result does not fit.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let two_half = Unwrapped(I16F16::from_num(2.5));
    /// assert_eq!(two_half.round_ties_to_even(), Unwrapped(I16F16::from_num(2)));
    /// let three_half = Unwrapped(I16F16::from_num(3.5));
    /// assert_eq!(three_half.round_ties_to_even(), Unwrapped(I16F16::from_num(4)));
    /// ```
    ///
    /// The following panics because of overflow.
    ///
    /// ```should_panic
    /// use fixed::{types::I16F16, Unwrapped};
    /// let max = Unwrapped(I16F16::MAX);
    /// let _overflow = max.round_ties_to_even();
    /// ```
    #[inline]
    pub fn round_ties_to_even(self) -> Unwrapped<F> {
        Unwrapped(self.0.unwrapped_round_ties_to_even())
    }

    /// Returns the number of ones in the binary representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let w = Unwrapped(I16F16::from_bits(0x00FF_FF00));
    /// assert_eq!(w.count_ones(), w.0.count_ones());
    /// ```
    #[inline]
    pub fn count_ones(self) -> u32 {
        self.0.count_ones()
    }

    /// Returns the number of zeros in the binary representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let w = Unwrapped(I16F16::from_bits(0x00FF_FF00));
    /// assert_eq!(w.count_zeros(), w.0.count_zeros());
    /// ```
    #[inline]
    pub fn count_zeros(self) -> u32 {
        self.0.count_zeros()
    }

    /// Returns the number of leading ones in the binary representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::U16F16, Unwrapped};
    /// let w = Unwrapped(U16F16::from_bits(0xFF00_00FF));
    /// assert_eq!(w.leading_ones(), w.0.leading_ones());
    /// ```
    #[inline]
    pub fn leading_ones(self) -> u32 {
        self.0.leading_ones()
    }

    /// Returns the number of leading zeros in the binary representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let w = Unwrapped(I16F16::from_bits(0x00FF_FF00));
    /// assert_eq!(w.leading_zeros(), w.0.leading_zeros());
    /// ```
    #[inline]
    pub fn leading_zeros(self) -> u32 {
        self.0.leading_zeros()
    }

    /// Returns the number of trailing ones in the binary representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::U16F16, Unwrapped};
    /// let w = Unwrapped(U16F16::from_bits(0xFF00_00FF));
    /// assert_eq!(w.trailing_ones(), w.0.trailing_ones());
    /// ```
    #[inline]
    pub fn trailing_ones(self) -> u32 {
        self.0.trailing_ones()
    }

    /// Returns the number of trailing zeros in the binary representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let w = Unwrapped(I16F16::from_bits(0x00FF_FF00));
    /// assert_eq!(w.trailing_zeros(), w.0.trailing_zeros());
    /// ```
    #[inline]
    pub fn trailing_zeros(self) -> u32 {
        self.0.trailing_zeros()
    }

    /// Integer base-2 logarithm, rounded down.
    ///
    /// # Panics
    ///
    /// Panics if the fixed-point number is ≤ 0.
    #[inline]
    pub fn int_log2(self) -> i32 {
        self.0.int_log2()
    }

    /// Integer base-10 logarithm, rounded down.
    ///
    /// # Panics
    ///
    /// Panics if the fixed-point number is ≤ 0.
    #[inline]
    pub fn int_log10(self) -> i32 {
        self.0.int_log10()
    }

    /// Reverses the order of the bits of the fixed-point number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let i = I16F16::from_bits(0x1234_5678);
    /// assert_eq!(Unwrapped(i).reverse_bits(), Unwrapped(i.reverse_bits()));
    /// ```
    #[inline]
    pub fn reverse_bits(self) -> Unwrapped<F> {
        Unwrapped(self.0.reverse_bits())
    }

    /// Shifts to the left by `n` bits, unwrapped the truncated bits to the right end.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let i = I16F16::from_bits(0x00FF_FF00);
    /// assert_eq!(Unwrapped(i).rotate_left(12), Unwrapped(i.rotate_left(12)));
    /// ```
    #[inline]
    pub fn rotate_left(self, n: u32) -> Unwrapped<F> {
        Unwrapped(self.0.rotate_left(n))
    }

    /// Shifts to the right by `n` bits, unwrapped the truncated bits to the left end.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let i = I16F16::from_bits(0x00FF_FF00);
    /// assert_eq!(Unwrapped(i).rotate_right(12), Unwrapped(i.rotate_right(12)));
    /// ```
    #[inline]
    pub fn rotate_right(self, n: u32) -> Unwrapped<F> {
        Unwrapped(self.0.rotate_right(n))
    }

    /// Returns the midpoint of `self` and `other`, rounding towards `self`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let three = Unwrapped(I16F16::from_num(3));
    /// let four = Unwrapped(I16F16::from_num(4));
    /// assert_eq!(three.midpoint(four), Unwrapped(I16F16::from_num(3.5)));
    /// assert_eq!(three.midpoint(-four), Unwrapped(I16F16::from_num(-0.5)));
    /// ```
    #[inline]
    pub fn midpoint(self, other: Unwrapped<F>) -> Unwrapped<F> {
        Unwrapped(self.0.midpoint(other.0))
    }

    /// Returns the reciprocal (inverse), 1/`self`.
    ///
    /// # Panics
    ///
    /// Panics if `self` is zero or on overflow.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I8F24, Unwrapped};
    /// let quarter = Unwrapped(I8F24::from_num(0.25));
    /// assert_eq!(quarter.recip(), Unwrapped(I8F24::from_num(4)));
    /// ```
    ///
    /// The following panics because of overflow.
    ///
    /// ```should_panic
    /// use fixed::{types::I8F24, Unwrapped};
    /// let frac_1_512 = Unwrapped(I8F24::from_num(1) / 512);
    /// let _overflow = frac_1_512.recip();
    /// ```
    #[inline]
    pub fn recip(self) -> Unwrapped<F> {
        Unwrapped(self.0.unwrapped_recip())
    }

    /// Multiply and add. Returns `self` × `mul` + `add`.
    ///
    /// # Panics
    ///
    /// Panics if the result does not fit.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let half = Unwrapped(I16F16::from_num(0.5));
    /// let three = Unwrapped(I16F16::from_num(3));
    /// let four = Unwrapped(I16F16::from_num(4));
    /// assert_eq!(three.mul_add(half, four), Unwrapped(I16F16::from_num(5.5)));
    /// // max × 1.5 − max = max / 2, which does not overflow
    /// let max = Unwrapped(I16F16::MAX);
    /// assert_eq!(max.mul_add(Unwrapped(I16F16::from_num(1.5)), -max), max / 2);
    /// ```
    ///
    /// The following panics because of overflow.
    ///
    /// ```should_panic
    /// use fixed::{types::I16F16, Unwrapped};
    /// let one = Unwrapped(I16F16::from_num(1));
    /// let max = Unwrapped(I16F16::MAX);
    /// let _overflow = max.mul_add(one, one);
    /// ```
    #[inline]
    pub fn mul_add(self, mul: Unwrapped<F>, add: Unwrapped<F>) -> Unwrapped<F> {
        Unwrapped(self.0.unwrapped_mul_add(mul.0, add.0))
    }

    /// Euclidean division.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero, or if the division results in overflow.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let num = Unwrapped(I16F16::from_num(7.5));
    /// let den = Unwrapped(I16F16::from_num(2));
    /// assert_eq!(num.div_euclid(den), Unwrapped(I16F16::from_num(3)));
    /// ```
    ///
    /// The following panics because of overflow.
    ///
    /// ```should_panic
    /// use fixed::{types::I16F16, Unwrapped};
    /// let quarter = Unwrapped(I16F16::from_num(0.25));
    /// let _overflow = Unwrapped(I16F16::MAX).div_euclid(quarter);
    /// ```
    #[inline]
    pub fn div_euclid(self, divisor: Unwrapped<F>) -> Unwrapped<F> {
        Unwrapped(self.0.unwrapped_div_euclid(divisor.0))
    }

    /// Remainder for Euclidean division.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let num = Unwrapped(I16F16::from_num(7.5));
    /// let den = Unwrapped(I16F16::from_num(2));
    /// assert_eq!(num.rem_euclid(den), Unwrapped(I16F16::from_num(1.5)));
    /// assert_eq!((-num).rem_euclid(den), Unwrapped(I16F16::from_num(0.5)));
    /// ```
    #[inline]
    pub fn rem_euclid(self, divisor: Unwrapped<F>) -> Unwrapped<F> {
        Unwrapped(self.0.rem_euclid(divisor.0))
    }

    /// Euclidean division by an integer.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero or if the division results in overflow.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let num = Unwrapped(I16F16::from_num(7.5));
    /// assert_eq!(num.div_euclid_int(2), Unwrapped(I16F16::from_num(3)));
    /// ```
    ///
    /// The following panics because of overflow.
    ///
    /// ```should_panic
    /// use fixed::{types::I16F16, Unwrapped};
    /// let min = Unwrapped(I16F16::MIN);
    /// let _overflow = min.div_euclid_int(-1);
    /// ```
    #[inline]
    pub fn div_euclid_int(self, divisor: F::Bits) -> Unwrapped<F> {
        Unwrapped(self.0.unwrapped_div_euclid_int(divisor))
    }

    /// Remainder for Euclidean division.
    ///
    /// # Panics
    ///
    /// Panics if the divisor is zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// let num = Unwrapped(I16F16::from_num(7.5));
    /// assert_eq!(num.rem_euclid_int(2), Unwrapped(I16F16::from_num(1.5)));
    /// assert_eq!((-num).rem_euclid_int(2), Unwrapped(I16F16::from_num(0.5)));
    /// ```
    ///
    /// The following panics because of overflow.
    ///
    /// ```should_panic
    /// use fixed::{types::I8F8, Unwrapped};
    /// let num = Unwrapped(I8F8::from_num(-7.5));
    /// // −128 ≤ Fix < 128, so the answer 192.5 overflows
    /// let _overflow = num.rem_euclid_int(200);
    /// ```
    #[inline]
    pub fn rem_euclid_int(self, divisor: F::Bits) -> Unwrapped<F> {
        Unwrapped(self.0.unwrapped_rem_euclid_int(divisor))
    }
}

impl<F: FixedSigned> Unwrapped<F> {
    /// Returns the number of bits required to represent the value.
    ///
    /// The number of bits required includes an initial one for
    /// negative numbers, and an initial zero for non-negative
    /// numbers.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I4F4, Unwrapped};
    /// assert_eq!(Unwrapped(I4F4::from_num(-3)).signed_bits(), 7);      // “_101.0000”
    /// assert_eq!(Unwrapped(I4F4::from_num(-1)).signed_bits(), 5);      // “___1.0000”
    /// assert_eq!(Unwrapped(I4F4::from_num(-0.0625)).signed_bits(), 1); // “____.___1”
    /// assert_eq!(Unwrapped(I4F4::from_num(0)).signed_bits(), 1);       // “____.___0”
    /// assert_eq!(Unwrapped(I4F4::from_num(0.0625)).signed_bits(), 2);  // “____.__01”
    /// assert_eq!(Unwrapped(I4F4::from_num(1)).signed_bits(), 6);       // “__01.0000”
    /// assert_eq!(Unwrapped(I4F4::from_num(3)).signed_bits(), 7);       // “_011.0000”
    /// ```
    #[inline]
    pub fn signed_bits(self) -> u32 {
        self.0.signed_bits()
    }

    /// Returns [`true`] if the number is > 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert!(Unwrapped(I16F16::from_num(4.3)).is_positive());
    /// assert!(!Unwrapped(I16F16::from_num(0)).is_positive());
    /// assert!(!Unwrapped(I16F16::from_num(-4.3)).is_positive());
    /// ```
    ///
    /// [`true`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    pub fn is_positive(self) -> bool {
        self.0.is_positive()
    }

    /// Returns [`true`] if the number is < 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert!(!Unwrapped(I16F16::from_num(4.3)).is_negative());
    /// assert!(!Unwrapped(I16F16::from_num(0)).is_negative());
    /// assert!(Unwrapped(I16F16::from_num(-4.3)).is_negative());
    /// ```
    ///
    /// [`true`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    pub fn is_negative(self) -> bool {
        self.0.is_negative()
    }

    /// Unwrapped absolute value. Returns the absolute value, panicking
    /// on overflow.
    ///
    /// Overflow can only occur when trying to find the absolute value
    /// of the minimum value.
    ///
    /// # Panics
    ///
    /// Panics if the result does not fit.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert_eq!(Unwrapped(I16F16::from_num(-5)).abs(), Unwrapped(I16F16::from_num(5)));
    /// ```
    ///
    /// The following panics because of overflow.
    ///
    /// ```should_panic
    /// use fixed::{types::I16F16, Unwrapped};
    /// let _overflow = Unwrapped(I16F16::MIN).abs();
    /// ```
    #[inline]
    pub fn abs(self) -> Unwrapped<F> {
        Unwrapped(self.0.unwrapped_abs())
    }

    /// Returns a number representing the sign of `self`.
    ///
    /// # Panics
    ///
    /// Panics
    ///   * if the value is positive and the fixed-point number has zero
    ///     or one integer bits such that it cannot hold the value 1.
    ///   * if the value is negative and the fixed-point number has zero
    ///     integer bits, such that it cannot hold the value −1.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::I16F16, Unwrapped};
    /// assert_eq!(Unwrapped(<I16F16>::from_num(-3.9)).signum(), Unwrapped(I16F16::from_num(-1)));
    /// assert_eq!(Unwrapped(<I16F16>::from_num(0)).signum(), Unwrapped(I16F16::from_num(0)));
    /// assert_eq!(Unwrapped(<I16F16>::from_num(3.9)).signum(), Unwrapped(I16F16::from_num(1)));
    /// ```
    ///
    /// The following panics because of overflow.
    ///
    /// ```should_panic
    /// use fixed::{types::I1F31, Unwrapped};
    /// let _overflow = Unwrapped(<I1F31>::from_num(0.5)).signum();
    /// ```
    #[inline]
    pub fn signum(self) -> Unwrapped<F> {
        Unwrapped(self.0.unwrapped_signum())
    }
}

impl<F: FixedUnsigned> Unwrapped<F> {
    /// Returns the number of bits required to represent the value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::U4F4, Unwrapped};
    /// assert_eq!(Unwrapped(U4F4::from_num(0)).significant_bits(), 0);      // “____.____”
    /// assert_eq!(Unwrapped(U4F4::from_num(0.0625)).significant_bits(), 1); // “____.___1”
    /// assert_eq!(Unwrapped(U4F4::from_num(1)).significant_bits(), 5);      // “___1.0000”
    /// assert_eq!(Unwrapped(U4F4::from_num(3)).significant_bits(), 6);      // “__11.0000”
    /// ```
    #[inline]
    pub fn significant_bits(self) -> u32 {
        self.0.significant_bits()
    }

    /// Returns [`true`] if the fixed-point number is
    /// 2<sup><i>k</i></sup> for some integer <i>k</i>.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::U16F16, Unwrapped};
    /// assert!(Unwrapped(U16F16::from_num(0.5)).is_power_of_two());
    /// assert!(Unwrapped(U16F16::from_num(4)).is_power_of_two());
    /// assert!(!Unwrapped(U16F16::from_num(5)).is_power_of_two());
    /// ```
    ///
    /// [`true`]: https://doc.rust-lang.org/nightly/std/primitive.bool.html
    #[inline]
    pub fn is_power_of_two(self) -> bool {
        self.0.is_power_of_two()
    }

    /// Returns the smallest power of two that is ≥ `self`.
    ///
    /// # Panics
    ///
    /// Panics if the next power of two is too large to fit.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fixed::{types::U16F16, Unwrapped};
    /// let half = Unwrapped(U16F16::from_num(0.5));
    /// assert_eq!(Unwrapped(U16F16::from_num(0.3)).next_power_of_two(), half);
    /// let four = Unwrapped(U16F16::from_num(4));
    /// assert_eq!(Unwrapped(U16F16::from_num(4)).next_power_of_two(), four);
    /// ```
    ///
    /// The following panics because of overflow.
    ///
    /// ```should_panic
    /// use fixed::{types::U16F16, Unwrapped};
    /// let _overflow = Unwrapped(U16F16::MAX).next_power_of_two();
    /// ```
    #[inline]
    pub fn next_power_of_two(self) -> Unwrapped<F> {
        Unwrapped(self.0.unwrapped_next_power_of_two())
    }
}

impl<F: Fixed> Display for Unwrapped<F> {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(&self.0, f)
    }
}

impl<F: Fixed> From<F> for Unwrapped<F> {
    /// Wraps a fixed-point number.
    #[inline]
    fn from(src: F) -> Unwrapped<F> {
        Unwrapped(src)
    }
}

impl<F: Fixed> FromStr for Unwrapped<F> {
    type Err = ParseFixedError;
    /// Parses a string slice containing decimal digits to return a fixed-point number.
    ///
    /// Rounding is to the nearest, with ties rounded to even.
    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        F::from_str(s).map(Unwrapped)
    }
}

macro_rules! op {
    ($unwrapped:ident, $Op:ident $op:ident, $OpAssign:ident $op_assign:ident) => {
        impl<F: Fixed> $Op<Unwrapped<F>> for Unwrapped<F> {
            type Output = Unwrapped<F>;
            #[inline]
            fn $op(self, other: Unwrapped<F>) -> Unwrapped<F> {
                Unwrapped((self.0).$unwrapped(other.0))
            }
        }
        impl<F: Fixed> $Op<Unwrapped<F>> for &Unwrapped<F> {
            type Output = Unwrapped<F>;
            #[inline]
            fn $op(self, other: Unwrapped<F>) -> Unwrapped<F> {
                Unwrapped((self.0).$unwrapped(other.0))
            }
        }
        impl<F: Fixed> $Op<&Unwrapped<F>> for Unwrapped<F> {
            type Output = Unwrapped<F>;
            #[inline]
            fn $op(self, other: &Unwrapped<F>) -> Unwrapped<F> {
                Unwrapped((self.0).$unwrapped(other.0))
            }
        }
        impl<F: Fixed> $Op<&Unwrapped<F>> for &Unwrapped<F> {
            type Output = Unwrapped<F>;
            #[inline]
            fn $op(self, other: &Unwrapped<F>) -> Unwrapped<F> {
                Unwrapped((self.0).$unwrapped(other.0))
            }
        }
        impl<F: Fixed> $OpAssign<Unwrapped<F>> for Unwrapped<F> {
            #[inline]
            fn $op_assign(&mut self, other: Unwrapped<F>) {
                self.0 = (self.0).$unwrapped(other.0);
            }
        }
        impl<F: Fixed> $OpAssign<&Unwrapped<F>> for Unwrapped<F> {
            #[inline]
            fn $op_assign(&mut self, other: &Unwrapped<F>) {
                self.0 = (self.0).$unwrapped(other.0);
            }
        }
    };
}

macro_rules! op_bitwise {
    ($Op:ident $op:ident, $OpAssign:ident $op_assign:ident) => {
        impl<F> $Op<Unwrapped<F>> for Unwrapped<F>
        where
            F: $Op<F, Output = F>,
        {
            type Output = Unwrapped<F>;
            #[inline]
            fn $op(self, other: Unwrapped<F>) -> Unwrapped<F> {
                Unwrapped((self.0).$op(other.0))
            }
        }
        impl<F> $Op<Unwrapped<F>> for &Unwrapped<F>
        where
            for<'a> &'a F: $Op<F, Output = F>,
        {
            type Output = Unwrapped<F>;
            #[inline]
            fn $op(self, other: Unwrapped<F>) -> Unwrapped<F> {
                Unwrapped((self.0).$op(other.0))
            }
        }
        impl<F> $Op<&Unwrapped<F>> for Unwrapped<F>
        where
            for<'a> F: $Op<&'a F, Output = F>,
        {
            type Output = Unwrapped<F>;
            #[inline]
            fn $op(self, other: &Unwrapped<F>) -> Unwrapped<F> {
                Unwrapped((self.0).$op(&other.0))
            }
        }
        impl<F> $Op<&Unwrapped<F>> for &Unwrapped<F>
        where
            for<'a, 'b> &'a F: $Op<&'b F, Output = F>,
        {
            type Output = Unwrapped<F>;
            #[inline]
            fn $op(self, other: &Unwrapped<F>) -> Unwrapped<F> {
                Unwrapped((self.0).$op(&other.0))
            }
        }
        impl<F> $OpAssign<Unwrapped<F>> for Unwrapped<F>
        where
            F: $OpAssign<F>,
        {
            #[inline]
            fn $op_assign(&mut self, other: Unwrapped<F>) {
                (self.0).$op_assign(other.0);
            }
        }
        impl<F> $OpAssign<&Unwrapped<F>> for Unwrapped<F>
        where
            for<'a> F: $OpAssign<&'a F>,
        {
            #[inline]
            fn $op_assign(&mut self, other: &Unwrapped<F>) {
                (self.0).$op_assign(&other.0);
            }
        }
    };
}

macro_rules! op_shift {
    (
        $Op:ident $op:ident, $OpAssign:ident $op_assign:ident;
        $($Rhs:ident),*
    ) => { $(
        impl<F> $Op<$Rhs> for Unwrapped<F>
        where
            F: $Op<u32, Output = F>,
        {
            type Output = Unwrapped<F>;
            #[inline]
            fn $op(self, other: $Rhs) -> Unwrapped<F> {
                let nbits = mem::size_of::<F>() as u32 * 8;
                let checked = other as u32 % nbits;
                assert!(checked as $Rhs == other, "overflow");
                Unwrapped((self.0).$op(checked))
            }
        }
        impl<F> $Op<$Rhs> for &Unwrapped<F>
        where
            for<'a> &'a F: $Op<u32, Output = F>,
        {
            type Output = Unwrapped<F>;
            #[inline]
            fn $op(self, other: $Rhs) -> Unwrapped<F> {
                let nbits = mem::size_of::<F>() as u32 * 8;
                let checked = other as u32 % nbits;
                assert!(checked as $Rhs == other, "overflow");
                Unwrapped((self.0).$op(checked))
            }
        }
        impl<F> $Op<&$Rhs> for Unwrapped<F>
        where
            F: $Op<u32, Output = F>,
        {
            type Output = Unwrapped<F>;
            #[inline]
            fn $op(self, other: &$Rhs) -> Unwrapped<F> {
                let nbits = mem::size_of::<F>() as u32 * 8;
                let checked = *other as u32 % nbits;
                assert!(checked as $Rhs == *other, "overflow");
                Unwrapped((self.0).$op(checked))
            }
        }
        impl<F> $Op<&$Rhs> for &Unwrapped<F>
        where
            for<'a> &'a F: $Op<u32, Output = F>,
        {
            type Output = Unwrapped<F>;
            #[inline]
            fn $op(self, other: &$Rhs) -> Unwrapped<F> {
                let nbits = mem::size_of::<F>() as u32 * 8;
                let checked = *other as u32 % nbits;
                assert!(checked as $Rhs == *other, "overflow");
                Unwrapped((self.0).$op(checked))
            }
        }
        impl<F> $OpAssign<$Rhs> for Unwrapped<F>
        where
            F: $OpAssign<u32>,
        {
            #[inline]
            fn $op_assign(&mut self, other: $Rhs) {
                let nbits = mem::size_of::<F>() as u32 * 8;
                let checked = other as u32 % nbits;
                assert!(checked as $Rhs == other, "overflow");
                (self.0).$op_assign(checked);
            }
        }
        impl<F> $OpAssign<&$Rhs> for Unwrapped<F>
        where
            F: $OpAssign<u32>,
        {
            #[inline]
            fn $op_assign(&mut self, other: &$Rhs) {
                let nbits = mem::size_of::<F>() as u32 * 8;
                let checked = *other as u32 % nbits;
                assert!(checked as $Rhs == *other, "overflow");
                (self.0).$op_assign(checked);
            }
        }
    )* };
}

impl<F: Fixed> Neg for Unwrapped<F> {
    type Output = Unwrapped<F>;
    #[inline]
    fn neg(self) -> Unwrapped<F> {
        Unwrapped((self.0).unwrapped_neg())
    }
}

impl<F: Fixed> Neg for &Unwrapped<F> {
    type Output = Unwrapped<F>;
    #[inline]
    fn neg(self) -> Unwrapped<F> {
        Unwrapped((self.0).unwrapped_neg())
    }
}
op! { unwrapped_add, Add add, AddAssign add_assign }
op! { unwrapped_sub, Sub sub, SubAssign sub_assign }
op! { unwrapped_mul, Mul mul, MulAssign mul_assign }
op! { unwrapped_div, Div div, DivAssign div_assign }
op! { rem, Rem rem, RemAssign rem_assign }

impl<F> Not for Unwrapped<F>
where
    F: Not<Output = F>,
{
    type Output = Unwrapped<F>;
    #[inline]
    fn not(self) -> Unwrapped<F> {
        Unwrapped((self.0).not())
    }
}
impl<F> Not for &Unwrapped<F>
where
    for<'a> &'a F: Not<Output = F>,
{
    type Output = Unwrapped<F>;
    #[inline]
    fn not(self) -> Unwrapped<F> {
        Unwrapped((self.0).not())
    }
}
op_bitwise! { BitAnd bitand, BitAndAssign bitand_assign }
op_bitwise! { BitOr bitor, BitOrAssign bitor_assign }
op_bitwise! { BitXor bitxor, BitXorAssign bitxor_assign }

op_shift! {
    Shl shl, ShlAssign shl_assign;
    i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
}
op_shift! {
    Shr shr, ShrAssign shr_assign;
    i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
}

impl<F: Fixed> Sum<Unwrapped<F>> for Unwrapped<F> {
    fn sum<I>(iter: I) -> Unwrapped<F>
    where
        I: Iterator<Item = Unwrapped<F>>,
    {
        iter.fold(Unwrapped(F::from_num(0)), Add::add)
    }
}

impl<'a, F: 'a + Fixed> Sum<&'a Unwrapped<F>> for Unwrapped<F> {
    fn sum<I>(iter: I) -> Unwrapped<F>
    where
        I: Iterator<Item = &'a Unwrapped<F>>,
    {
        iter.fold(Unwrapped(F::from_num(0)), Add::add)
    }
}

impl<F: Fixed> Product<Unwrapped<F>> for Unwrapped<F> {
    fn product<I>(mut iter: I) -> Unwrapped<F>
    where
        I: Iterator<Item = Unwrapped<F>>,
    {
        match iter.next() {
            None => match 1.overflowing_to_fixed() {
                (_, true) => panic!("overflow"),
                (ans, false) => Unwrapped(ans),
            },
            Some(first) => iter.fold(first, Mul::mul),
        }
    }
}

impl<'a, F: 'a + Fixed> Product<&'a Unwrapped<F>> for Unwrapped<F> {
    fn product<I>(mut iter: I) -> Unwrapped<F>
    where
        I: Iterator<Item = &'a Unwrapped<F>>,
    {
        match iter.next() {
            None => match 1.overflowing_to_fixed() {
                (_, true) => panic!("overflow"),
                (ans, false) => Unwrapped(ans),
            },
            Some(first) => iter.fold(*first, Mul::mul),
        }
    }
}

// The following cannot be implemented for Unwrapped<F> where F: Fixed,
// otherwise there will be a conflicting implementation error. For
// example we cannot implement both these without triggering E0119:
//
//     impl<F: Fixed> Op<F::Bits> for Unwrapped<F> { /* ... */ }
//     impl<F: Fixed> Op<&F::Bits> for Unwrapped<F> { /* ... */ }
//
// To work around this, we provide implementations like this:
//
//     impl<Frac> Op<i8> for Unwrapped<FixedI8<Frac>> { /* ... */ }
//     impl<Frac> Op<&i8> for Unwrapped<FixedI8<Frac>> { /* ... */ }
//     impl<Frac> Op<i16> for Unwrapped<FixedI16<Frac>> { /* ... */ }
//     impl<Frac> Op<&i16> for Unwrapped<FixedI16<Frac>> { /* ... */ }
//     ...

macro_rules! op_bits {
    (
        $Fixed:ident($Bits:ident $(, $LeEqU:ident)*)::$unwrapped:ident,
        $Op:ident $op:ident,
        $OpAssign:ident $op_assign:ident
    ) => {
        impl<Frac $(: $LeEqU)*> $Op<$Bits> for Unwrapped<$Fixed<Frac>> {
            type Output = Unwrapped<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: $Bits) -> Unwrapped<$Fixed<Frac>> {
                Unwrapped((self.0).$unwrapped(other))
            }
        }
        impl<Frac $(: $LeEqU)*> $Op<$Bits> for &Unwrapped<$Fixed<Frac>> {
            type Output = Unwrapped<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: $Bits) -> Unwrapped<$Fixed<Frac>> {
                Unwrapped((self.0).$unwrapped(other))
            }
        }
        impl<Frac $(: $LeEqU)*> $Op<&$Bits> for Unwrapped<$Fixed<Frac>> {
            type Output = Unwrapped<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &$Bits) -> Unwrapped<$Fixed<Frac>> {
                Unwrapped((self.0).$unwrapped(*other))
            }
        }
        impl<Frac $(: $LeEqU)*> $Op<&$Bits> for &Unwrapped<$Fixed<Frac>> {
            type Output = Unwrapped<$Fixed<Frac>>;
            #[inline]
            fn $op(self, other: &$Bits) -> Unwrapped<$Fixed<Frac>> {
                Unwrapped((self.0).$unwrapped(*other))
            }
        }
        impl<Frac $(: $LeEqU)*> $OpAssign<$Bits> for Unwrapped<$Fixed<Frac>> {
            #[inline]
            fn $op_assign(&mut self, other: $Bits) {
                self.0 = (self.0).$unwrapped(other);
            }
        }
        impl<Frac $(: $LeEqU)*> $OpAssign<&$Bits> for Unwrapped<$Fixed<Frac>> {
            #[inline]
            fn $op_assign(&mut self, other: &$Bits) {
                self.0 = (self.0).$unwrapped(*other);
            }
        }
    };
}

macro_rules! ops {
    ($Fixed:ident($Bits:ident, $LeEqU:ident)) => {
        op_bits! { $Fixed($Bits)::unwrapped_mul_int, Mul mul, MulAssign mul_assign }
        op_bits! { $Fixed($Bits)::unwrapped_div_int, Div div, DivAssign div_assign }
        op_bits! { $Fixed($Bits, $LeEqU)::rem, Rem rem, RemAssign rem_assign }
    };
}
ops! { FixedI8(i8, LeEqU8) }
ops! { FixedI16(i16, LeEqU16) }
ops! { FixedI32(i32, LeEqU32) }
ops! { FixedI64(i64, LeEqU64) }
ops! { FixedI128(i128, LeEqU128) }
ops! { FixedU8(u8, LeEqU8) }
ops! { FixedU16(u16, LeEqU16) }
ops! { FixedU32(u32, LeEqU32) }
ops! { FixedU64(u64, LeEqU64) }
ops! { FixedU128(u128, LeEqU128) }
