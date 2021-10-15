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
use az_crate::WrappingAs;

pub struct U256 {
    pub lo: u128,
    pub hi: u128,
}

pub struct I256 {
    pub lo: u128,
    pub hi: i128,
}

#[inline]
pub fn u256_wrapping_as_i256(a: U256) -> I256 {
    I256 {
        lo: a.lo,
        hi: a.hi.wrapping_as::<i128>(),
    }
}

#[inline]
pub fn wrapping_add_u256_u128(a: U256, b: u128) -> U256 {
    let (lo, carry) = a.lo.overflowing_add(b);
    let hi = a.hi.wrapping_add(u128::from(carry));
    U256 { lo, hi }
}

#[inline]
pub fn overflowing_add_u128_u256(a: u128, b: U256) -> (u128, bool) {
    let (lo, carry) = a.overflowing_add(b.lo);
    (lo, carry | (b.hi != 0))
}

#[inline]
pub fn overflowing_sub_u128_u256(a: u128, b: U256) -> (u128, bool) {
    let (lo, borrow) = a.overflowing_sub(b.lo);
    (lo, borrow | (b.hi != 0))
}

#[inline]
pub fn wrapping_neg_u256(a: U256) -> U256 {
    let (lo, carry) = (!a.lo).overflowing_add(1);
    let hi = (!a.hi).wrapping_add(u128::from(carry));
    U256 { lo, hi }
}

#[inline]
pub fn overflowing_add_i256_i128(a: I256, b: i128) -> (I256, bool) {
    let b = I256 {
        lo: b.wrapping_as::<u128>(),
        hi: b >> 127,
    };
    let (lo, carry) = a.lo.overflowing_add(b.lo);
    // b.hi is in {-1, 0}, and carry is in {0, 1}, so we can add them wrappingly
    let b_hi_plus_carry = b.hi.wrapping_add(i128::from(carry));
    let (hi, overflow) = a.hi.overflowing_add(b_hi_plus_carry);
    (I256 { lo, hi }, overflow)
}

#[inline]
pub fn wide_mul_u128(a: u128, b: u128) -> U256 {
    let (lo, hi) = arith::mul_u128(a, b);
    U256 { lo, hi }
}

#[inline]
pub fn shl_u256_max_128(a: U256, sh: u32) -> U256 {
    if sh == 0 {
        a
    } else if sh == 128 {
        U256 { lo: a.hi, hi: 0 }
    } else {
        U256 {
            lo: (a.lo >> sh) | (a.hi << (128 - sh)),
            hi: a.hi >> sh,
        }
    }
}
