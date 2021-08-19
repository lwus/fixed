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
    helpers::{ToFixedHelper, Widest},
    traits::Fixed,
    types::extra::{Bit, False, True, U0},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    cmp::Ordering,
    fmt::{Debug, Display},
    ops::{Add, BitAnd, BitOr, Div, Not, Rem, Shl, Shr, Sub},
};

pub trait IntHelper
where
    Self: Copy + Ord + Debug + Display,
    Self: Shl<u32, Output = Self> + Shr<u32, Output = Self>,
    Self: Not<Output = Self> + BitAnd<Output = Self> + BitOr<Output = Self>,
    Self: Add<Output = Self> + Sub<Output = Self> + Div<Output = Self> + Rem<Output = Self>,
{
    type IsSigned: Bit;
    type Unsigned: IntHelper;
    type ReprFixed: Fixed;

    const BITS: u32;
    const MSB: Self;
    const ZERO: Self;

    fn is_negative(self) -> bool;
    fn is_odd(self) -> bool;
    fn checked_inc(self) -> Option<Self>;
    fn overflowing_add(self, val: Self) -> (Self, bool);
    fn overflowing_mul(self, val: Self) -> (Self, bool);
    fn leading_zeros(self) -> u32;
    fn trailing_zeros(self) -> u32;

    fn to_fixed_helper(
        self,
        src_frac_bits: i32,
        dst_frac_bits: u32,
        dst_int_bits: u32,
    ) -> ToFixedHelper;

    fn to_repr_fixed(self) -> Self::ReprFixed;
    fn from_repr_fixed(src: Self::ReprFixed) -> Self;

    fn neg_abs(self) -> (bool, Self::Unsigned);
    fn from_neg_abs(neg: bool, abs: Self::Unsigned) -> Self;
}

macro_rules! sealed_int {
    ($Int:ident($IsSigned:ident, $Unsigned:ty, $ReprFixed:ident); $($rest:tt)*) => {
        impl IntHelper for $Int {
            type IsSigned = $IsSigned;
            type Unsigned = $Unsigned;
            type ReprFixed = $ReprFixed<U0>;

            const BITS: u32 = $Int::BITS;
            const MSB: $Int = 1 << ($Int::BITS - 1);
            const ZERO: $Int = 0;

            #[inline]
            fn checked_inc(self) -> Option<$Int> {
                self.checked_add(1)
            }

            #[inline]
            fn overflowing_add(self, val: $Int) -> ($Int, bool) {
                self.overflowing_add(val)
            }

            #[inline]
            fn overflowing_mul(self, val: $Int) -> ($Int, bool) {
                self.overflowing_mul(val)
            }

            #[inline]
            fn leading_zeros(self) -> u32 {
                self.leading_zeros()
            }

            #[inline]
            fn trailing_zeros(self) -> u32 {
                self.trailing_zeros()
            }

            #[inline]
            fn to_repr_fixed(self) -> Self::ReprFixed {
                Self::ReprFixed::from_bits(self.int_repr())
            }

            #[inline]
            fn from_repr_fixed(src: Self::ReprFixed) -> Self {
                IntRepr::from_int_repr(src.to_bits())
            }

            $($rest)*
        }
    };
    ($Unsigned:ident($ReprFixed:ident)) => {
        sealed_int! {
            $Unsigned(False, $Unsigned, $ReprFixed);

            #[inline]
            fn is_negative(self) -> bool {
                false
            }

            #[inline]
            fn is_odd(self) -> bool {
                self & 1 != 0
            }

            #[inline]
            fn neg_abs(self) -> (bool, Self::Unsigned) {
                (false, self)
            }

            #[inline]
            fn from_neg_abs(neg: bool, abs: Self::Unsigned) -> Self {
                debug_assert!(!neg || abs == 0);
                let _ = neg;
                abs
            }

            #[inline]
            fn to_fixed_helper(
                self,
                src_frac_bits: i32,
                dst_frac_bits: u32,
                dst_int_bits: u32,
            ) -> ToFixedHelper {
                let src_bits = Self::BITS as i32;
                let dst_bits = (dst_frac_bits + dst_int_bits) as i32;

                if self == 0 {
                    return ToFixedHelper {
                        bits:Widest::Unsigned(0),
                        dir:Ordering::Equal,
                        overflow:false,
                    };
                }

                let leading_zeros = self.leading_zeros();
                let need_to_shr = src_frac_bits - dst_frac_bits as i32;
                let overflow = src_bits - dst_bits > need_to_shr + leading_zeros as i32;
                let bits_128 = u128::from(self.int_repr());
                let (bits, lost_bits) = match need_to_shr {
                    -0x7fff_ffff..=-128 => (0, false),
                    -127..=-1 => (bits_128 << -need_to_shr, false),
                    0 => (bits_128, false),
                    1..=127 => {
                        let shifted = bits_128 >> need_to_shr;
                        (shifted, shifted << need_to_shr != bits_128)
                    }
                    128..=0x7fff_ffff => (0, true),
                    _ => unreachable!(),
                };
                let dir = if lost_bits { Ordering::Less } else { Ordering::Equal };
                ToFixedHelper {
                    bits: Widest::Unsigned(bits),
                    dir,
                    overflow,
                }
            }
        }
    };
    ($Signed:ident($Unsigned:ty, $ReprFixed:ident)) => {
        sealed_int! {
            $Signed(True, $Unsigned, $ReprFixed);

            #[inline]
            fn is_negative(self) -> bool {
                self < 0
            }

            #[inline]
            fn is_odd(self) -> bool {
                self & 1 != 0
            }

            #[inline]
            fn neg_abs(self) -> (bool, Self::Unsigned) {
                if self < 0 {
                    (true, self.wrapping_neg() as $Unsigned)
                } else {
                    (false, self as $Unsigned)
                }
            }

            #[inline]
            fn from_neg_abs(neg: bool, abs: Self::Unsigned) -> Self {
                debug_assert!(abs <= Self::Unsigned::MSB);
                if neg {
                    abs.wrapping_neg() as Self
                } else {
                    abs as Self
                }
            }

            #[inline]
            fn to_fixed_helper(
                self,
                src_frac_bits: i32,
                dst_frac_bits: u32,
                dst_int_bits: u32,
            ) -> ToFixedHelper {
                let src_bits = Self::BITS as i32;
                let dst_bits = (dst_frac_bits + dst_int_bits) as i32;

                if self == 0 {
                    return ToFixedHelper {
                        bits: Widest::Unsigned(0),
                        dir: Ordering::Equal,
                        overflow: false,
                    };
                }

                let need_to_shr = src_frac_bits - dst_frac_bits as i32;
                let leading = if self >= 0 {
                    self.leading_zeros()
                } else {
                    (!self).leading_zeros() - 1
                };
                let overflow = src_bits - dst_bits > need_to_shr + leading as i32;
                let bits_128 = i128::from(self.int_repr());
                let (bits, lost_bits) = match need_to_shr {
                    -0x7fff_ffff..=-128 => (0, false),
                    -127..=-1 => (bits_128 << -need_to_shr, false),
                    0 => (bits_128, false),
                    1..=127 => {
                        let shifted = bits_128 >> need_to_shr;
                        (shifted, shifted << need_to_shr != bits_128)
                    }
                    128..=0x7fff_ffff => (bits_128 >> 127, true),
                    _ => unreachable!(),
                };
                let dir = if lost_bits { Ordering::Less } else { Ordering::Equal };
                let bits = if self >= 0 {
                    Widest::Unsigned(bits as u128)
                } else {
                    Widest::Negative(bits)
                };
                ToFixedHelper { bits, dir, overflow }
            }
        }
    };
}

sealed_int! { i8(u8, FixedI8) }
sealed_int! { i16(u16, FixedI16) }
sealed_int! { i32(u32, FixedI32) }
sealed_int! { i64(u64, FixedI64) }
sealed_int! { i128(u128, FixedI128) }
#[cfg(target_pointer_width = "16")]
sealed_int! { isize(usize, FixedI16) }
#[cfg(target_pointer_width = "32")]
sealed_int! { isize(usize, FixedI32) }
#[cfg(target_pointer_width = "64")]
sealed_int! { isize(usize, FixedI64) }
sealed_int! { u8(FixedU8) }
sealed_int! { u16(FixedU16) }
sealed_int! { u32(FixedU32) }
sealed_int! { u64(FixedU64) }
sealed_int! { u128(FixedU128) }
#[cfg(target_pointer_width = "16")]
sealed_int! { usize(FixedU16) }
#[cfg(target_pointer_width = "32")]
sealed_int! { usize(FixedU32) }
#[cfg(target_pointer_width = "64")]
sealed_int! { usize(FixedU64) }

trait IntRepr: Copy {
    type Int;
    fn int_repr(self) -> Self::Int;
    fn from_int_repr(i: Self::Int) -> Self;
}

macro_rules! int_repr {
    ($T:ident) => {
        impl IntRepr for $T {
            type Int = $T;
            #[inline]
            fn int_repr(self) -> $T {
                self
            }
            #[inline]
            fn from_int_repr(i: $T) -> $T {
                i
            }
        }
    };
    ($T:ident($Int:ident)) => {
        impl IntRepr for $T {
            type Int = $Int;
            #[inline]
            fn int_repr(self) -> $Int {
                self as $Int
            }
            #[inline]
            fn from_int_repr(i: $Int) -> $T {
                i as $T
            }
        }
    };
}

int_repr! { i8 }
int_repr! { i16 }
int_repr! { i32 }
int_repr! { i64 }
int_repr! { i128 }
#[cfg(target_pointer_width = "16")]
int_repr! { isize(i16) }
#[cfg(target_pointer_width = "32")]
int_repr! { isize(i32) }
#[cfg(target_pointer_width = "64")]
int_repr! { isize(i64) }
int_repr! { u8 }
int_repr! { u16 }
int_repr! { u32 }
int_repr! { u64 }
int_repr! { u128 }
#[cfg(target_pointer_width = "16")]
int_repr! { usize(u16) }
#[cfg(target_pointer_width = "32")]
int_repr! { usize(u32) }
#[cfg(target_pointer_width = "64")]
int_repr! { usize(u64) }
