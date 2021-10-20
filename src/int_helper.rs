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
    traits::Fixed,
    types::extra::{Bit, False, True, U0},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use core::{
    fmt::{Debug, Display},
    ops::{Add, BitAnd, BitOr, Div, Not, Rem, Shl, Shr, Sub},
};

macro_rules! make_helper_common {
    ($t:ident) => {
        use crate::helpers::{ToFixedHelper, Widest};
        use core::cmp::Ordering;
    };
}
macro_rules! make_helper {
    ($i: ident, $u:ident) => {
        pub mod $i {
            make_helper_common! { $i }

            #[inline]
            pub fn neg_abs(val: $i) -> (bool, $u) {
                if val < 0 {
                    (true, val.wrapping_neg() as $u)
                } else {
                    (false, val as $u)
                }
            }

            #[inline]
            pub fn is_negative(val: $i) -> bool {
                val.is_negative()
            }

            #[inline]
            pub fn to_fixed_helper(
                val: $i,
                src_frac_bits: i32,
                dst_frac_bits: u32,
                dst_int_bits: u32,
            ) -> ToFixedHelper {
                let src_bits = $i::BITS as i32;
                let dst_bits = (dst_frac_bits + dst_int_bits) as i32;

                if val == 0 {
                    return ToFixedHelper {
                        bits: Widest::Unsigned(0),
                        dir: Ordering::Equal,
                        overflow: false,
                    };
                }

                let need_to_shr = src_frac_bits - dst_frac_bits as i32;
                let leading = if val >= 0 {
                    val.leading_zeros()
                } else {
                    (!val).leading_zeros() - 1
                };
                let overflow = src_bits - dst_bits > need_to_shr + leading as i32;
                let bits_128 = i128::from(val);
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
                let dir = if lost_bits {
                    Ordering::Less
                } else {
                    Ordering::Equal
                };
                let bits = if val >= 0 {
                    Widest::Unsigned(bits as u128)
                } else {
                    Widest::Negative(bits)
                };
                ToFixedHelper {
                    bits,
                    dir,
                    overflow,
                }
            }
        }

        pub mod $u {
            make_helper_common! { $u }

            #[inline]
            pub fn neg_abs(val: $u) -> (bool, $u) {
                (false, val)
            }

            #[inline]
            pub fn is_negative(val: $u) -> bool {
                let _ = val;
                false
            }

            #[inline]
            pub fn to_fixed_helper(
                val: $u,
                src_frac_bits: i32,
                dst_frac_bits: u32,
                dst_int_bits: u32,
            ) -> ToFixedHelper {
                let src_bits = $u::BITS as i32;
                let dst_bits = (dst_frac_bits + dst_int_bits) as i32;

                if val == 0 {
                    return ToFixedHelper {
                        bits: Widest::Unsigned(0),
                        dir: Ordering::Equal,
                        overflow: false,
                    };
                }

                let leading_zeros = val.leading_zeros();
                let need_to_shr = src_frac_bits - dst_frac_bits as i32;
                let overflow = src_bits - dst_bits > need_to_shr + leading_zeros as i32;
                let bits_128 = u128::from(val);
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
                let dir = if lost_bits {
                    Ordering::Less
                } else {
                    Ordering::Equal
                };
                ToFixedHelper {
                    bits: Widest::Unsigned(bits),
                    dir,
                    overflow,
                }
            }
        }
    };
}

make_helper! { i8, u8 }
make_helper! { i16, u16 }
make_helper! { i32, u32 }
make_helper! { i64, u64 }
make_helper! { i128, u128 }

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

    fn is_odd(self) -> bool;
    fn checked_inc(self) -> Option<Self>;
    fn overflowing_add(self, val: Self) -> (Self, bool);
    fn overflowing_mul(self, val: Self) -> (Self, bool);
    fn leading_zeros(self) -> u32;
    fn trailing_zeros(self) -> u32;

    fn to_repr_fixed(self) -> Self::ReprFixed;
    fn from_repr_fixed(src: Self::ReprFixed) -> Self;
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
            fn is_odd(self) -> bool {
                self & 1 != 0
            }
        }
    };
    ($Signed:ident($Unsigned:ty, $ReprFixed:ident)) => {
        sealed_int! {
            $Signed(True, $Unsigned, $ReprFixed);

            #[inline]
            fn is_odd(self) -> bool {
                self & 1 != 0
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
