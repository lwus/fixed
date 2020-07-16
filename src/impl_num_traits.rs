// Copyright © 2018–2020 Trevor Spiteri

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
    types::extra::{
        IsLessOrEqual, LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8, True, U126, U127, U14, U15,
        U30, U31, U6, U62, U63, U7,
    },
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};
use num_traits::{
    bounds::Bounded,
    identities::{One, Zero},
    ops::{
        checked::{
            CheckedAdd, CheckedDiv, CheckedMul, CheckedNeg, CheckedRem, CheckedShl, CheckedShr,
            CheckedSub,
        },
        saturating::{SaturatingAdd, SaturatingMul, SaturatingSub},
        wrapping::{WrappingAdd, WrappingMul, WrappingNeg, WrappingShl, WrappingShr, WrappingSub},
    },
};

macro_rules! impl_traits {
    ($Fixed:ident, $LeEqU:ident, $OneMaxFrac:ident) => {
        impl<Frac> Bounded for $Fixed<Frac> {
            #[inline]
            fn min_value() -> Self {
                Self::MIN
            }
            #[inline]
            fn max_value() -> Self {
                Self::MAX
            }
        }

        impl<Frac> Zero for $Fixed<Frac> {
            #[inline]
            fn zero() -> Self {
                Self::from_bits(0)
            }
            #[inline]
            fn is_zero(&self) -> bool {
                self.to_bits() == 0
            }
        }

        impl<Frac: $LeEqU> One for $Fixed<Frac>
        where
            Frac: IsLessOrEqual<$OneMaxFrac, Output = True>,
        {
            #[inline]
            fn one() -> Self {
                Self::from_bits(Self::from_bits(1).to_bits() << Frac::U32)
            }
        }

        impl<Frac> CheckedAdd for $Fixed<Frac> {
            #[inline]
            fn checked_add(&self, v: &Self) -> Option<Self> {
                (*self).checked_add(*v)
            }
        }

        impl<Frac> CheckedSub for $Fixed<Frac> {
            #[inline]
            fn checked_sub(&self, v: &Self) -> Option<Self> {
                (*self).checked_sub(*v)
            }
        }

        impl<Frac> CheckedNeg for $Fixed<Frac> {
            #[inline]
            fn checked_neg(&self) -> Option<Self> {
                (*self).checked_neg()
            }
        }

        impl<Frac: $LeEqU> CheckedMul for $Fixed<Frac> {
            #[inline]
            fn checked_mul(&self, v: &Self) -> Option<Self> {
                (*self).checked_mul(*v)
            }
        }

        impl<Frac: $LeEqU> CheckedDiv for $Fixed<Frac> {
            #[inline]
            fn checked_div(&self, v: &Self) -> Option<Self> {
                (*self).checked_div(*v)
            }
        }

        impl<Frac> CheckedRem for $Fixed<Frac> {
            #[inline]
            fn checked_rem(&self, v: &Self) -> Option<Self> {
                (*self).checked_rem(*v)
            }
        }

        impl<Frac> CheckedShl for $Fixed<Frac> {
            #[inline]
            fn checked_shl(&self, rhs: u32) -> Option<Self> {
                (*self).checked_shl(rhs)
            }
        }

        impl<Frac> CheckedShr for $Fixed<Frac> {
            #[inline]
            fn checked_shr(&self, rhs: u32) -> Option<Self> {
                (*self).checked_shr(rhs)
            }
        }

        impl<Frac> SaturatingAdd for $Fixed<Frac> {
            #[inline]
            fn saturating_add(&self, v: &Self) -> Self {
                (*self).saturating_add(*v)
            }
        }

        impl<Frac> SaturatingSub for $Fixed<Frac> {
            #[inline]
            fn saturating_sub(&self, v: &Self) -> Self {
                (*self).saturating_sub(*v)
            }
        }

        impl<Frac: $LeEqU> SaturatingMul for $Fixed<Frac> {
            #[inline]
            fn saturating_mul(&self, v: &Self) -> Self {
                (*self).saturating_mul(*v)
            }
        }

        impl<Frac> WrappingAdd for $Fixed<Frac> {
            #[inline]
            fn wrapping_add(&self, v: &Self) -> Self {
                (*self).wrapping_add(*v)
            }
        }

        impl<Frac> WrappingSub for $Fixed<Frac> {
            #[inline]
            fn wrapping_sub(&self, v: &Self) -> Self {
                (*self).wrapping_sub(*v)
            }
        }

        impl<Frac> WrappingNeg for $Fixed<Frac> {
            #[inline]
            fn wrapping_neg(&self) -> Self {
                (*self).wrapping_neg()
            }
        }

        impl<Frac: $LeEqU> WrappingMul for $Fixed<Frac> {
            #[inline]
            fn wrapping_mul(&self, v: &Self) -> Self {
                (*self).wrapping_mul(*v)
            }
        }

        impl<Frac> WrappingShl for $Fixed<Frac> {
            #[inline]
            fn wrapping_shl(&self, rhs: u32) -> Self {
                (*self).wrapping_shl(rhs)
            }
        }

        impl<Frac> WrappingShr for $Fixed<Frac> {
            #[inline]
            fn wrapping_shr(&self, rhs: u32) -> Self {
                (*self).wrapping_shr(rhs)
            }
        }
    };
}

impl_traits! { FixedI8, LeEqU8, U6 }
impl_traits! { FixedI16, LeEqU16, U14 }
impl_traits! { FixedI32, LeEqU32, U30 }
impl_traits! { FixedI64, LeEqU64, U62 }
impl_traits! { FixedI128, LeEqU128, U126 }
impl_traits! { FixedU8, LeEqU8, U7 }
impl_traits! { FixedU16, LeEqU16, U15 }
impl_traits! { FixedU32, LeEqU32, U31 }
impl_traits! { FixedU64, LeEqU64, U63 }
impl_traits! { FixedU128, LeEqU128, U127 }
