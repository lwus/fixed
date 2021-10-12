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

use crate::arith;
use az_crate::{OverflowingAs, WrappingAs};

macro_rules! make_lerp {
    ($i:ident, $u:ident, $ii:ident, $uu:ident, $uu1:expr) => {
        pub fn $i(r: $i, start: $i, end: $i, frac_bits: u32) -> ($i, bool) {
            // 0x00 ≤ r_abs ≤ 0x80
            let (r_abs, r_neg) = if r >= 0 {
                (r.wrapping_as::<$u>(), false)
            } else {
                (r.wrapping_neg().wrapping_as::<$u>(), true)
            };
            // 0x00 ≤ range_abs ≤ 0xff
            let (range_abs, range_neg) = if end >= start {
                (end.wrapping_sub(start).wrapping_as::<$u>(), false)
            } else {
                (start.wrapping_sub(end).wrapping_as::<$u>(), true)
            };
            // 0x0000 ≤ wide_abs ≤ 0x7f80
            let wide_abs = $uu::from(r_abs) * $uu::from(range_abs);
            let wide_neg = r_neg != range_neg;
            let wide_uns = if wide_neg {
                // 0x0000 ≤ add ≤ 0x00ff
                let add = ($uu1 << frac_bits) - 1;
                // If frac_bits is 0: add = 0x0000; 0x0000 ≤ shifted ≤ 0x7f80
                // If frac_bits is max: add = 0x00ff; 0x0000 ≤ shifted ≤ 0x0080
                let shifted = (wide_abs + add) >> frac_bits;
                shifted.wrapping_neg()
            } else {
                wide_abs >> frac_bits
            };
            let wide = wide_uns.wrapping_as::<$ii>();
            let (wide_ret, overflow1) = wide.overflowing_add($ii::from(start));
            let (ret, overflow2) = wide_ret.overflowing_as::<$i>();
            (ret, overflow1 | overflow2)
        }

        pub fn $u(r: $u, start: $u, end: $u, frac_bits: u32) -> ($u, bool) {
            // 0x00 ≤ range_abs ≤ 0xff
            let (range_abs, range_neg) = if end >= start {
                (end - start, false)
            } else {
                (start - end, true)
            };
            // 0x0000 ≤ wide_abs ≤  0xfe01
            let wide_abs = $uu::from(r) * $uu::from(range_abs);
            let (wide_ret, overflow1) = if range_neg {
                // 0x0000 ≤ add ≤ 0x00ff
                let add = ($uu1 << frac_bits) - 1;
                // If frac_bits is 0: add = 0x0000; 0x0000 ≤ shifted ≤ 0xfe01
                // If frac_bits is max: add = 0x00ff; 0x0000 ≤ shifted ≤ 0x00ff
                let shifted = (wide_abs + add) >> frac_bits;
                $uu::from(start).overflowing_sub(shifted)
            } else {
                let shifted = wide_abs >> frac_bits;
                $uu::from(start).overflowing_add(shifted)
            };
            let (ret, overflow2) = wide_ret.overflowing_as::<$u>();
            (ret, overflow1 | overflow2)
        }
    };
}

make_lerp! { i8, u8, i16, u16, 1u16 }
make_lerp! { i16, u16, i32, u32, 1u32 }
make_lerp! { i32, u32, i64, u64, 1u64 }
make_lerp! { i64, u64, i128, u128, 1u128 }

pub fn i128(r: i128, start: i128, end: i128, frac_bits: u32) -> (i128, bool) {
    // 0x00 ≤ r_abs ≤ 0x80
    let (r_abs, r_neg) = if r >= 0 {
        (r.wrapping_as::<u128>(), false)
    } else {
        (r.wrapping_neg().wrapping_as::<u128>(), true)
    };
    // 0x00 ≤ range_abs ≤ 0xff
    let (range_abs, range_neg) = if end >= start {
        (end.wrapping_sub(start).wrapping_as::<u128>(), false)
    } else {
        (start.wrapping_sub(end).wrapping_as::<u128>(), true)
    };
    // 0x0000 ≤ wide_abs ≤ 0x7f80
    let (wide_abs_lo, wide_abs_hi) = arith::mul_u128(r_abs, range_abs);
    let wide_neg = r_neg != range_neg;
    let (wide_uns_lo, wide_uns_hi) = if wide_neg {
        // 0x0000 ≤ add ≤ 0x00ff
        let add = if frac_bits == 128 {
            u128::MAX
        } else {
            (1u128 << frac_bits) - 1
        };
        // If frac_bits is 0: add = 0x0000; 0x0000 ≤ shifted ≤ 0x7f80
        // If frac_bits is max: add = 0x00ff; 0x0000 ≤ shifted ≤ 0x0080
        let (sum_lo, carry) = wide_abs_lo.overflowing_add(add);
        let sum_hi = wide_abs_hi + u128::from(carry);
        let (shifted_lo, shifted_hi) = if frac_bits == 0 {
            (sum_lo, sum_hi)
        } else if frac_bits == 128 {
            (sum_hi, 0)
        } else {
            (
                (sum_lo >> frac_bits) | (sum_hi << (128 - frac_bits)),
                sum_hi >> frac_bits,
            )
        };
        let (neg_lo, carry) = (!shifted_lo).overflowing_add(1);
        let neg_hi = (!shifted_hi).wrapping_add(u128::from(carry));
        (neg_lo, neg_hi)
    } else if frac_bits == 0 {
        (wide_abs_lo, wide_abs_hi)
    } else if frac_bits == 128 {
        (wide_abs_hi, 0)
    } else {
        (
            (wide_abs_lo >> frac_bits) | (wide_abs_hi << (128 - frac_bits)),
            wide_abs_hi >> frac_bits,
        )
    };
    let start_lo = start.wrapping_as::<u128>();
    let start_hi = start >> 127;
    let wide_lo = wide_uns_lo;
    let wide_hi = wide_uns_hi.wrapping_as::<i128>();
    let (wide_ret_lo, carry) = wide_lo.overflowing_add(start_lo);
    // start_hi is in {-1, 0}, and carry is in {0, 1}, so we can add them wrappingly
    let start_hi_plus_carry = start_hi.wrapping_add(i128::from(carry));
    let (wide_ret_hi, overflow1) = wide_hi.overflowing_add(start_hi_plus_carry);
    let ret = wide_ret_lo.wrapping_as::<i128>();
    let overflow2 = if ret < 0 {
        wide_ret_hi != -1
    } else {
        wide_ret_hi != 0
    };
    (ret, overflow1 | overflow2)
}

pub fn u128(r: u128, start: u128, end: u128, frac_bits: u32) -> (u128, bool) {
    // 0x00 ≤ range_abs ≤ 0xff
    let (range_abs, range_neg) = if end >= start {
        (end - start, false)
    } else {
        (start - end, true)
    };
    // 0x0000 ≤ wide_abs ≤  0xfe01
    let (wide_abs_lo, wide_abs_hi) = arith::mul_u128(r, range_abs);
    let (wide_ret_lo, wide_ret_hi, overflow1) = if range_neg {
        // 0x0000 ≤ add ≤ 0x00ff
        let add = if frac_bits == 128 {
            u128::MAX
        } else {
            (1u128 << frac_bits) - 1
        };
        // If frac_bits is 0: add = 0x0000; 0x0000 ≤ shifted ≤ 0xfe01
        // If frac_bits is max: add = 0x00ff; 0x0000 ≤ shifted ≤ 0x00ff
        let (sum_lo, carry) = wide_abs_lo.overflowing_add(add);
        let sum_hi = wide_abs_hi + u128::from(carry);
        let (shifted_lo, shifted_hi) = if frac_bits == 0 {
            (sum_lo, sum_hi)
        } else if frac_bits == 128 {
            (sum_hi, 0)
        } else {
            (
                (sum_lo >> frac_bits) | (sum_hi << (128 - frac_bits)),
                sum_hi >> frac_bits,
            )
        };
        let (wide_ret_lo, borrow) = start.overflowing_sub(shifted_lo);
        let (wide_ret_hi, overflow1) = shifted_hi.overflowing_neg();
        (wide_ret_lo, wide_ret_hi, borrow | overflow1)
    } else {
        let (shifted_lo, shifted_hi) = if frac_bits == 0 {
            (wide_abs_lo, wide_abs_hi)
        } else if frac_bits == 128 {
            (wide_abs_hi, 0)
        } else {
            (
                (wide_abs_lo >> frac_bits) | (wide_abs_hi << (128 - frac_bits)),
                wide_abs_hi >> frac_bits,
            )
        };
        let (wide_ret_lo, carry) = start.overflowing_add(shifted_lo);
        let (wide_ret_hi, overflow1) = u128::from(carry).overflowing_add(shifted_hi);
        (wide_ret_lo, wide_ret_hi, overflow1)
    };
    let ret = wide_ret_lo;
    let overflow2 = wide_ret_hi != 0;
    (ret, overflow1 | overflow2)
}
