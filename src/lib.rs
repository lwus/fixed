// Copyright © 2018 Trevor Spiteri

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

/*!
# Fixed-point numbers

The [*fixed* crate] provides fixed-point numbers. Currently it uses
the [*typenum* crate] for the fractional bit count; it is planned to
move to [const generics] when they are implemented by the Rust
compiler.

The crate provides the following types:

  * [`FixedI8`] is a signed eight-bit fixed-point number,
  * [`FixedI16`] is a signed 16-bit fixed-point number,
  * [`FixedI32`] is a signed 32-bit fixed-point number,
  * [`FixedI64`] is a signed 64-bit fixed-point number,
  * [`FixedI128`] is a signed 128-bit fixed-point number,
  * [`FixedU8`] is an unsigned eight-bit fixed-point number,
  * [`FixedU16`] is an unsigned 16-bit fixed-point number,
  * [`FixedU32`] is an unsigned 32-bit fixed-point number,
  * [`FixedU64`] is an unsigned 64-bit fixed-point number, and
  * [`FixedU128`] is an unsigned 128-bit fixed-point number.

All fixed-point numbers can have `Frac` fractional bits, where `Frac`
can have any value from 0 up to and including the size of the number
in bits. When `Frac` is 0, the fixed-point number behaves like an
integer. When `Frac` is equal to the number of bits, the value of the
fixed-point number lies in the range −0.5 ≤ *x* < 0.5 for signed
fixed-point numbers, and in the range 0 ≤ *x* < 1 for unsigned
fixed-point numbers.

## Quick example

```rust
use fixed::frac;
use fixed::FixedI32;

// 20 integer bits, 12 fractional bits
type I20F12 = FixedI32<frac::U12>;
// 19/3 = 6 1/3
let six_and_third = I20F12::from_int(19).unwrap() / 3;
// four decimal digits for 12 binary digits
assert_eq!(six_and_third.to_string(), "6.3333");
// convert to i32, taking the ceil
assert_eq!(six_and_third.to_int_ceil(), 7);
```

## Using the *fixed* crate

The *fixed* crate is available on [crates.io][*fixed* crate]. To use
it in your crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
fixed = "0.1.0"
```

You also need to declare it by adding this to your crate root (usually
*lib.rs* or *main.rs*):

```rust
extern crate fixed;
```

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
[*fixed* crate]: https://crates.io/crates/fixed
[*typenum* crate]: https://crates.io/crates/typenum
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[`FixedI128`]: struct.FixedI128.html
[`FixedI16`]: struct.FixedI16.html
[`FixedI32`]: struct.FixedI32.html
[`FixedI64`]: struct.FixedI64.html
[`FixedI8`]: struct.FixedI8.html
[`FixedU128`]: struct.FixedU128.html
[`FixedU16`]: struct.FixedU16.html
[`FixedU32`]: struct.FixedU32.html
[`FixedU64`]: struct.FixedU64.html
[`FixedU8`]: struct.FixedU8.html
[channels]: https://doc.rust-lang.org/book/second-edition/appendix-07-nightly-rust.html
[const generics]: https://github.com/rust-lang/rust/issues/44580
*/
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/fixed/0.1.0")]
#![doc(test(attr(deny(warnings))))]
#![cfg_attr(nightly_repr_transparent, feature(repr_transparent))]

extern crate typenum;

mod display;
pub mod frac;
mod helper;

use frac::Unsigned;
use helper::FixedHelper;
use std::cmp::Ordering;
use std::f32;
use std::f64;
use std::hash::{Hash, Hasher};
use std::iter::{Product, Sum};
use std::marker::PhantomData;
use std::mem;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

macro_rules! if_signed {
    (Signed => $($rem:tt)+) => {
        $($rem)+
    };
    (Unsigned => $($rem:tt)+) => {
    };
}
macro_rules! if_unsigned {
    (Signed => $($rem:tt)+) => {
    };
    (Unsigned => $($rem:tt)+) => {
        $($rem)+
    };
}

macro_rules! refs {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<'a, Frac: Unsigned> $Imp<$Fixed<Frac>> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp<$Fixed<Frac>>>::$method(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> $Imp<&'a $Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp<$Fixed<Frac>>>::$method(self, *rhs)
            }
        }

        impl<'a, 'b, Frac: Unsigned> $Imp<&'a $Fixed<Frac>> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp<$Fixed<Frac>>>::$method(*self, *rhs)
            }
        }
    };
}

macro_rules! refs_assign {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<'a, Frac: Unsigned> $Imp<&'a $Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: &$Fixed<Frac>) {
                <$Fixed<Frac> as $Imp<$Fixed<Frac>>>::$method(self, *rhs);
            }
        }
    };
}

macro_rules! pass {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<Frac: Unsigned> $Imp<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner as $Imp<$Inner>>::$method(
                    self.to_bits(),
                    rhs.to_bits(),
                ))
            }
        }

        refs! { impl $Imp for $Fixed($Inner) { $method } }
    };
}

macro_rules! pass_assign {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<Frac: Unsigned> $Imp<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: $Fixed<Frac>) {
                <$Inner as $Imp<$Inner>>::$method(&mut self.to_bits(), rhs.to_bits());
            }
        }

        refs_assign! { impl $Imp for $Fixed($Inner) { $method } }
    };
}

macro_rules! pass_one {
    (impl $Imp:ident for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<Frac: Unsigned> $Imp for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner as $Imp>::$method(self.to_bits()))
            }
        }

        impl<'a, Frac: Unsigned> $Imp for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp>::$method(*self)
            }
        }
    };
}

macro_rules! pass_method {
    ($comment:expr, $Fixed:ident($Inner:ty) => fn $method:ident()) => {
        #[doc = $comment]
        #[inline]
        pub fn $method() -> $Fixed<Frac> {
            $Fixed::from_bits(<$Inner>::$method())
        }
    };
    ($comment:expr, $Fixed:ident($Inner:ty) => fn $method:ident(self)) => {
        #[doc = $comment]
        #[inline]
        pub fn $method(self) -> $Fixed<Frac> {
            $Fixed::from_bits(<$Inner>::$method(self.to_bits()))
        }
    };
    ($comment:expr, $Fixed:ident($Inner:ty) => fn $method:ident(self) -> $ret_ty:ty) => {
        #[doc = $comment]
        #[inline]
        pub fn $method(self) -> $ret_ty {
            <$Inner>::$method(self.to_bits())
        }
    };
    (
        $comment:expr,
        $Fixed:ident($Inner:ty) => fn $method:ident(self, $param:ident: $param_ty:ty)
    ) => {
        #[doc = $comment]
        #[inline]
        pub fn $method(self, $param: $param_ty) -> $Fixed<Frac> {
            $Fixed::from_bits(<$Inner>::$method(self.to_bits(), $param))
        }
    };
}

macro_rules! shift {
    (impl $Imp:ident < $Rhs:ty > for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<Frac: Unsigned> $Imp<$Rhs> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Rhs) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner as $Imp<$Rhs>>::$method(self.to_bits(), rhs))
            }
        }

        impl<'a, Frac: Unsigned> $Imp<$Rhs> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: $Rhs) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp<$Rhs>>::$method(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> $Imp<&'a $Rhs> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Rhs) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp<$Rhs>>::$method(self, *rhs)
            }
        }

        impl<'a, 'b, Frac: Unsigned> $Imp<&'a $Rhs> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn $method(self, rhs: &$Rhs) -> $Fixed<Frac> {
                <$Fixed<Frac> as $Imp<$Rhs>>::$method(*self, *rhs)
            }
        }
    };
}

macro_rules! shift_assign {
    (impl $Imp:ident < $Rhs:ty > for $Fixed:ident($Inner:ty) { $method:ident }) => {
        impl<Frac: Unsigned> $Imp<$Rhs> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: $Rhs) {
                <$Inner as $Imp<$Rhs>>::$method(&mut self.to_bits(), rhs);
            }
        }

        impl<'a, Frac: Unsigned> $Imp<&'a $Rhs> for $Fixed<Frac> {
            #[inline]
            fn $method(&mut self, rhs: &$Rhs) {
                <$Fixed<Frac> as $Imp<$Rhs>>::$method(self, *rhs);
            }
        }
    };
}

macro_rules! shift_all {
    (
        impl {$Imp:ident, $ImpAssign:ident}<{$($Rhs:ty),*}>
            for $Fixed:ident($Inner:ty)
        { $method:ident, $method_assign:ident }
    ) => { $(
        shift! { impl $Imp<$Rhs> for $Fixed($Inner) { $method } }
        shift_assign! { impl $ImpAssign<$Rhs> for $Fixed($Inner) { $method_assign } }
    )* };
}

macro_rules! doc_comment {
    ($x:expr, $($tt:tt)*) => {
        #[doc = $x]
        $($tt)*
    };
}

macro_rules! doc_comment_signed_unsigned {
    ($Signedness:tt, $signed:expr, $unsigned:expr, $($tt:tt)*) => {
        if_signed! { $Signedness => doc_comment! { $signed, $($tt)* } }
        if_unsigned! { $Signedness => doc_comment! { $unsigned, $($tt)* } }
    };
}

macro_rules! to_f {
    ($method:ident -> $f:ident($u:ident), $exp_bits:expr, $prec:expr) => {
        doc_comment! {
            concat!(
                "Converts the fixed-point number to `", stringify!($f), "`."
            ),
            pub fn $method(self) -> $f {
                // exponent is IEEE754 style (1 <= significand < 2)
                let exp_max = (1 << ($exp_bits - 1)) - 1;
                let exp_min = 1 - exp_max;
                let (int_bits, frac_bits) = (Self::int_bits(), Self::frac_bits());

                let (neg, int, frac) = self.parts();
                let int_frac = (int << frac_bits) | (frac >> int_bits);
                let leading_zeros = int_frac.leading_zeros();
                let signif_bits = int_bits + frac_bits - leading_zeros;
                if signif_bits == 0 {
                    debug_assert!(!neg);
                    return 0.0;
                }
                // remove leading zeros and implicit one
                let mut mantissa = int_frac << leading_zeros << 1;
                let exponent = int_bits as i32 - 1 - leading_zeros as i32;
                let biased_exponent = if exponent > exp_max {
                    return if neg { $f::NEG_INFINITY } else { $f::INFINITY };
                } else if exponent < exp_min {
                    let lost_prec = exp_min - exponent;
                    if lost_prec as u32 >= (int_bits + frac_bits) {
                        mantissa = 0;
                    } else {
                        // reinsert implicit one
                        mantissa = (mantissa >> 1) | !(!0 >> 1);
                        mantissa >>= lost_prec - 1;
                    }
                    0
                } else {
                    (exponent + exp_max) as $u
                };
                // check for rounding
                let round_up = (int_bits + frac_bits >= $prec) && {
                    let shift = $prec - 1;
                    let mid_bit = !(!0 >> 1) >> shift;
                    let lower_bits = mid_bit - 1;
                    if mantissa & mid_bit == 0 {
                        false
                    } else if mantissa & lower_bits != 0 {
                        true
                    } else {
                        // round to even
                        mantissa & (mid_bit << 1) != 0
                    }
                };
                let bits_sign = if neg { !(!0 >> 1) } else { 0 };
                let bits_exp = biased_exponent << ($prec - 1);
                let bits_mantissa = (if int_bits + frac_bits >= $prec - 1 {
                    (mantissa >> (int_bits + frac_bits - ($prec - 1))) as $u
                } else {
                    (mantissa as $u) << ($prec - 1 - (int_bits + frac_bits))
                }) & !(!0 << ($prec - 1));
                let mut bits_exp_mantissa = bits_exp | bits_mantissa;
                if round_up {
                    // cannot be infinite already, so we won't get NaN
                    debug_assert!(bits_exp_mantissa != $f::INFINITY.to_bits());
                    bits_exp_mantissa += 1;
                }
                $f::from_bits(bits_sign | bits_exp_mantissa)
            }
        }
    };
}

macro_rules! fixed {
    ($description:expr, $Fixed:ident($Inner:ty, $bits_count:expr), $Signedness:tt) => {
        doc_comment! {
            concat!(
                $description,
                "\nwith `Frac` fractional bits.\n",
                "\n",
                "Currently `Frac` is an [`Unsigned`] as provided by\n",
                "the [typenum crate]; it is planned to move to\n",
                "[const generics] when they are implemented by the\n",
                "Rust compiler.\n",
                "\n",
                "# Examples\n",
                "\n",
                "```rust\n",
                "use fixed::frac::U3;\n",
                "use fixed::", stringify!($Fixed), ";\n",
                "let eleven = ", stringify!($Fixed), "::<U3>::from_bits(11 << 3);\n",
                "let five_half = eleven >> 1u32;\n",
                "assert_eq!(eleven.to_string(), \"11.0\");\n",
                "assert_eq!(five_half.to_string(), \"5.5\");\n",
                "```\n",
                "\n",
                "[`Unsigned`]: https://docs.rs/typenum/^1.3/typenum/marker_traits/trait.Unsigned.html\n",
                "[const generics]: https://github.com/rust-lang/rust/issues/44580\n",
                "[typenum crate]: https://crates.io/crates/typenum\n"
            ),
            #[cfg_attr(repr_transparent, repr(transparent))]
            pub struct $Fixed<Frac: Unsigned>(($Inner, PhantomData<Frac>));
        }

        impl<Frac: Unsigned> Clone for $Fixed<Frac> {
            fn clone(&self) -> $Fixed<Frac> {
                $Fixed::from_bits(self.to_bits())
            }
        }

        impl<Frac: Unsigned> Copy for $Fixed<Frac> {}

        impl<Frac: Unsigned> Default for $Fixed<Frac> {
            fn default() -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner as Default>::default())
            }
        }

        impl<Frac: Unsigned> Eq for $Fixed<Frac> {}

        impl<Frac: Unsigned> PartialEq<$Fixed<Frac>> for $Fixed<Frac> {
            fn eq(&self, rhs: &$Fixed<Frac>) -> bool {
                self.to_bits().eq(&rhs.to_bits())
            }
        }

        impl<Frac: Unsigned> Ord for $Fixed<Frac> {
            fn cmp(&self, rhs: &$Fixed<Frac>) -> Ordering {
                self.to_bits().cmp(&rhs.to_bits())
            }
        }

        impl<Frac: Unsigned> PartialOrd<$Fixed<Frac>> for $Fixed<Frac> {
            fn partial_cmp(&self, rhs: &$Fixed<Frac>) -> Option<Ordering> {
                self.to_bits().partial_cmp(&rhs.to_bits())
            }
        }

        impl<Frac: Unsigned> Hash for $Fixed<Frac> {
            fn hash<H>(&self, state: &mut H)
            where
                H: Hasher
            {
                self.to_bits().hash(state);
            }
        }

        impl<Frac: Unsigned> $Fixed<Frac> {
            pass_method! {
                "Returns the smallest value that can be represented.",
                $Fixed($Inner) => fn min_value()
            }
            pass_method! {
                "Returns the largest value that can be represented.",
                $Fixed($Inner) => fn max_value()
            }

            /// Returns the number of integer bits.
            #[inline]
            pub fn int_bits() -> u32 {
                <$Fixed<Frac> as FixedHelper<Frac>>::bits() - <$Fixed<Frac>>::frac_bits()
            }

            /// Returns the number of fractional bits.
            #[inline]
            pub fn frac_bits() -> u32 {
                Frac::to_u32()
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number of type `", stringify!($Fixed), "`\n",
                    "that has a bitwise representation identical to the\n",
                    "`", stringify!($Inner), "` value."
                ),
                #[inline]
                pub fn from_bits(v: $Inner) -> $Fixed<Frac> {
                    let bits = <$Fixed<Frac> as FixedHelper<Frac>>::bits();
                    assert!(Frac::to_u32() <= bits, "`Frac` too large");
                    $Fixed((v, PhantomData))
                }
            }

            doc_comment! {
                concat!(
                    "Creates an integer of type `", stringify!($Inner), "`\n",
                    "that has a bitwise representation identical to the\n",
                    "`", stringify!($Fixed), "` value."
                ),
                #[inline]
                pub fn to_bits(self) -> $Inner {
                    (self.0).0
                }
            }

            doc_comment! {
                concat!(
                    "Creates a fixed-point number of type `", stringify!($Fixed), "`\n",
                    "that has the same value as an integer of type\n",
                    "`", stringify!($Inner), "` if it fits.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let fix_one = Fix::from_bits(1 << 4);\n",
                    "assert_eq!(Fix::from_int(1), Some(fix_one));\n",
                    "let too_large = 1 << (", stringify!($bits_count), " - 2);\n",
                    "assert_eq!(Fix::from_int(too_large), None);\n",
                    "```\n"
                ),
                #[inline]
                pub fn from_int(v: $Inner) -> Option<$Fixed<Frac>> {
                    let frac_bits = <$Fixed<Frac>>::frac_bits();
                    let bits = v.checked_shl(frac_bits).unwrap_or(0);
                    let all_frac_check;
                    if_signed! { $Signedness => all_frac_check = bits >> (frac_bits - 1); }
                    if_unsigned! { $Signedness => all_frac_check = 0; }

                    let check = bits.checked_shr(frac_bits).unwrap_or(all_frac_check);
                    if check == v {
                        Some($Fixed::from_bits(bits))
                    } else {
                        None
                    }
                }
            }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` truncating the fractional bits.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int(), 2);\n",
                    "let neg_two_half = -two_half;\n",
                    "assert_eq!(neg_two_half.to_int(), -2);\n",
                    "```\n"
                ),
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` truncating the fractional bits.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int(), 2);\n",
                    "```\n"
                ),
                #[inline]
                pub fn to_int(self) -> $Inner {
                    let floor = self.to_int_floor();
                    if_signed! { $Signedness => {
                        let no_frac = self.frac().to_bits() == 0;
                        if no_frac || self.to_bits() >= 0 {
                            floor
                        } else {
                            floor + 1
                        }
                    } }
                    if_unsigned! { $Signedness => {
                        floor
                    } }
                }
            }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` rounding towards +∞.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int_ceil(), 3);\n",
                    "let neg_two_half = -two_half;\n",
                    "assert_eq!(neg_two_half.to_int_ceil(), -2);\n",
                    "```\n"
                ),
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` rounding towards +∞.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int_ceil(), 3);\n",
                    "```\n"
                ),
                #[inline]
                pub fn to_int_ceil(self) -> $Inner {
                    let floor = self.to_int_floor();
                    let no_frac = self.frac().to_bits() == 0;
                    if no_frac {
                        floor
                    } else {
                        floor + 1
                    }
                }
            }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` rounding towards −∞.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int_floor(), 2);\n",
                    "let neg_two_half = -two_half;\n",
                    "assert_eq!(neg_two_half.to_int_floor(), -3);\n",
                    "```\n"
                ),
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` rounding towards −∞.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int_floor(), 2);\n",
                    "```\n"
                ),
                #[inline]
                pub fn to_int_floor(self) -> $Inner {
                    let bits = self.to_bits();
                    if Self::int_bits() == 0 {
                        if_signed! { $Signedness => bits >> (Self::frac_bits() - 1) }
                        if_unsigned! { $Signedness => 0 }
                    } else {
                        bits >> Self::frac_bits()
                    }
                }
            }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` rounding towards the nearest.\n",
                    "Ties are rounded away from zero.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int_round(), 3);\n",
                    "let neg_two_half = -two_half;\n",
                    "assert_eq!(neg_two_half.to_int_round(), -3);\n",
                    "let one_quarter = two_half / 2;\n",
                    "assert_eq!(one_quarter.to_int_round(), 1);\n",
                    "```\n"
                ),
                concat!(
                    "Converts the fixed-point number of type `", stringify!($Fixed), "`\n",
                    "to an integer of type\n",
                    "`", stringify!($Inner), "` rounding towards −∞.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "let two_half = Fix::from_int(5).unwrap() / 2;\n",
                    "assert_eq!(two_half.to_int_round(), 3);\n",
                    "let one_quarter = two_half / 2;\n",
                    "assert_eq!(one_quarter.to_int_round(), 1);\n",
                    "```\n"
                ),
                #[inline]
                pub fn to_int_round(self) -> $Inner {
                    let frac_bits = <$Fixed<Frac>>::frac_bits();
                    let floor = self.to_int_floor();
                    if frac_bits == 0 {
                        return floor;
                    }
                    let half_bit = 1 << (frac_bits - 1);
                    if_signed! { $Signedness => {
                        if self.to_bits() >= 0 {
                            if (self.to_bits() & half_bit) != 0 {
                                floor + 1
                            } else {
                                floor
                            }
                        } else {
                            let neg =  self.to_bits().wrapping_neg();
                            if (neg & half_bit) != 0 {
                                floor
                            } else {
                                floor + 1
                            }
                        }
                    } }
                    if_unsigned! { $Signedness => {
                        if (self.to_bits() & half_bit) != 0 {
                            floor + 1
                        } else {
                            floor
                        }
                    } }
                }
            }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Returns the integer part.\n",
                    "\n",
                    "Note that since the numbers are stored in two’s\n",
                    "complement, negative numbers with non-zero fractional\n",
                    "parts will be rounded towards −∞, except in the case\n",
                    "where there are no integer bits, that is `",
                    stringify!($Fixed), "<U", stringify!($bits_count), ">`,\n",
                    "where the return value is always zero.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 0010.0000\n",
                    "let two = Fix::from_int(2).unwrap();\n",
                    "// 0010.0100\n",
                    "let two_and_quarter = two + two / 8;\n",
                    "assert_eq!(two_and_quarter.int(), two);\n",
                    "// 1101.0000\n",
                    "let neg_three = Fix::from_int(-3).unwrap();\n",
                    "// 1101.1100\n",
                    "let neg_two_and_quarter = -two_and_quarter;\n",
                    "assert_eq!(neg_two_and_quarter.int(), neg_three);\n",
                    "```\n"
                ),
                concat!(
                    "Returns the integer part.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 0010.0000\n",
                    "let two = Fix::from_int(2).unwrap();\n",
                    "// 0010.0100\n",
                    "let two_and_quarter = two + two / 8;\n",
                    "assert_eq!(two_and_quarter.int(), two);\n",
                    "```\n"
                ),
                #[inline]
                pub fn int(self) -> $Fixed<Frac> {
                    let frac_bits = <$Fixed<Frac>>::frac_bits();
                    let mask = <$Inner>::checked_shl(!0, frac_bits).unwrap_or(0);
                    $Fixed::from_bits(self.to_bits() & mask)
                }
            }

            doc_comment_signed_unsigned! {
                $Signedness,
                concat!(
                    "Returns the fractional part.\n",
                    "\n",
                    "Note that since the numbers are stored in two’s\n",
                    "complement, the returned fraction will be non-negative\n",
                    "for negative numbers, except in the case where\n",
                    "there are no integer bits, that is `",
                    stringify!($Fixed), "<U", stringify!($bits_count), ">`,\n",
                    "where the return value is always equal to `self`.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 0000.0100\n",
                    "let quarter = Fix::from_int(1).unwrap() / 4;\n",
                    "// 0010.0100\n",
                    "let two_and_quarter = quarter * 9;\n",
                    "assert_eq!(two_and_quarter.frac(), quarter);\n",
                    "// 0000.1100\n",
                    "let three_quarters = quarter * 3;\n",
                    "// 1101.1100\n",
                    "let neg_two_and_quarter = -two_and_quarter;\n",
                    "assert_eq!(neg_two_and_quarter.frac(), three_quarters);\n",
                    "```\n"
                ),
                concat!(
                    "Returns the fractional part.\n",
                    "\n",
                    "# Examples\n",
                    "\n",
                    "```rust\n",
                    "use fixed::frac;\n",
                    "use fixed::", stringify!($Fixed), ";\n",
                    "type Fix = ", stringify!($Fixed), "<frac::U4>;\n",
                    "// 0000.0100\n",
                    "let quarter = Fix::from_int(1).unwrap() / 4;\n",
                    "// 0010.0100\n",
                    "let two_and_quarter = quarter * 9;\n",
                    "assert_eq!(two_and_quarter.frac(), quarter);\n",
                    "```\n"
                ),
                #[inline]
                pub fn frac(self) -> $Fixed<Frac> {
                    let frac_bits = <$Fixed<Frac>>::frac_bits();
                    let inv_mask = <$Inner>::checked_shl(!0, frac_bits).unwrap_or(0);
                    $Fixed::from_bits(self.to_bits() & !inv_mask)
                }
            }

            to_f! { to_f32 -> f32(u32), 8, 24 }
            to_f! { to_f64 -> f64(u64), 11, 53 }

            pass_method! {
                "Returns the number of ones in the binary representation.",
                $Fixed($Inner) => fn count_ones(self) -> u32
            }
            pass_method! {
                "Returns the number of zeros in the binary representation.",
                $Fixed($Inner) => fn count_zeros(self) -> u32
            }
            pass_method! {
                "Returns the number of leading zeros in the binary representation.",
                $Fixed($Inner) => fn leading_zeros(self) -> u32
            }
            pass_method! {
                "Returns the number of trailing zeros in the binary representation.",
                $Fixed($Inner) => fn trailing_zeros(self) -> u32
            }
            pass_method! {
                "Shifts to the left by `n` bits, wrapping the truncated bits to the right end.",
                $Fixed($Inner) => fn rotate_left(self, n: u32)
            }
            pass_method! {
                "Shifts to the right by `n` bits, wrapping the truncated bits to the left end.",
                $Fixed($Inner) => fn rotate_right(self, n: u32)
            }

            /// Checked negation.
            #[inline]
            pub fn checked_neg(self) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_neg(self.to_bits()).map($Fixed::from_bits)
            }

            /// Checked fixed-point addition.
            #[inline]
            pub fn checked_add(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_add(self.to_bits(), rhs.to_bits()).map($Fixed::from_bits)
            }

            /// Checked fixed-point subtraction.
            #[inline]
            pub fn checked_sub(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_sub(self.to_bits(), rhs.to_bits()).map($Fixed::from_bits)
            }

            /// Checked fixed-point multiplication.
            #[inline]
            pub fn checked_mul(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::to_u32());
                match dir {
                    Ordering::Equal => Some($Fixed::from_bits(ans)),
                    _ => None,
                }
            }

            /// Checked fixed-point division.
            #[inline]
            pub fn checked_div(self, rhs: $Fixed<Frac>) -> Option<$Fixed<Frac>> {
                if rhs.to_bits() == 0 {
                    return None;
                }
                let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::to_u32());
                match dir {
                    Ordering::Equal => Some($Fixed::from_bits(ans)),
                    _ => None,
                }
            }

            /// Checked fixed-point multiplication by integer.
            #[inline]
            pub fn checked_mul_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_mul(self.to_bits(), rhs).map($Fixed::from_bits)
            }

            /// Checked fixed-point division by integer.
            #[inline]
            pub fn checked_div_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_div(self.to_bits(), rhs).map($Fixed::from_bits)
            }

            /// Checked fixed-point remainder for division by integer.
            #[inline]
            pub fn checked_rem_int(self, rhs: $Inner) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_rem(self.to_bits(), rhs).map($Fixed::from_bits)
            }

            /// Checked fixed-point left shift.
            #[inline]
            pub fn checked_shl(self, rhs: u32) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_shl(self.to_bits(), rhs).map($Fixed::from_bits)
            }

            /// Checked fixed-point right shift.
            #[inline]
            pub fn checked_shr(self, rhs: u32) -> Option<$Fixed<Frac>> {
                <$Inner>::checked_shr(self.to_bits(), rhs).map($Fixed::from_bits)
            }

            if_signed! {
                $Signedness =>
                /// Checked absolute value.
                #[inline]
                pub fn checked_abs(self) -> Option<$Fixed<Frac>> {
                    <$Inner>::checked_abs(self.to_bits()).map($Fixed::from_bits)
                }
            }

            /// Saturating fixed-point addition.
            #[inline]
            pub fn saturating_add(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::saturating_add(self.to_bits(), rhs.to_bits()))
            }

            /// Saturating fixed-point subtraction.
            #[inline]
            pub fn saturating_sub(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::saturating_sub(self.to_bits(), rhs.to_bits()))
            }

            /// Saturating fixed-point multiplication.
            #[inline]
            pub fn saturating_mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::to_u32());
                match dir {
                    Ordering::Equal => $Fixed::from_bits(ans),
                    Ordering::Less => $Fixed::max_value(),
                    Ordering::Greater => $Fixed::min_value(),
                }
            }

            /// Saturating fixed-point division.
            #[inline]
            pub fn saturating_div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::to_u32());
                match dir {
                    Ordering::Equal => $Fixed::from_bits(ans),
                    Ordering::Less => $Fixed::max_value(),
                    Ordering::Greater => $Fixed::min_value(),
                }
            }

            /// Saturating fixed-point multiplication by integer.
            #[inline]
            pub fn saturating_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::saturating_mul(self.to_bits(), rhs))
            }

            /// Wrapping negation.
            #[inline]
            pub fn wrapping_neg(self) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_neg(self.to_bits()))
            }

            /// Wrapping fixed-point addition.
            #[inline]
            pub fn wrapping_add(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_add(self.to_bits(), rhs.to_bits()))
            }

            /// Wrapping fixed-point subtraction.
            #[inline]
            pub fn wrapping_sub(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_sub(self.to_bits(), rhs.to_bits()))
            }

            /// Wrapping fixed-point multiplication.
            #[inline]
            pub fn wrapping_mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, _dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::to_u32());
                $Fixed::from_bits(ans)
            }

            /// Wrapping fixed-point division.
            #[inline]
            pub fn wrapping_div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, _dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::to_u32());
                $Fixed::from_bits(ans)
            }

            /// Wrapping fixed-point multiplication by integer.
            #[inline]
            pub fn wrapping_mul_int(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_mul(self.to_bits(), rhs))
            }

            /// Wrapping fixed-point division by integer.
            #[inline]
            pub fn wrapping_div_int(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_div(self.to_bits(), rhs))
            }

            /// Wrapping fixed-point remainder for division by integer.
            #[inline]
            pub fn wrapping_rem_int(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_rem(self.to_bits(), rhs))
            }

            /// Wrapping fixed-point left shift.
            #[inline]
            pub fn wrapping_shl(self, rhs: u32) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_shl(self.to_bits(), rhs))
            }

            /// Wrapping fixed-point right shift.
            #[inline]
            pub fn wrapping_shr(self, rhs: u32) -> $Fixed<Frac> {
                $Fixed::from_bits(<$Inner>::wrapping_shr(self.to_bits(), rhs))
            }

            if_signed! {
                $Signedness =>
                /// Wrapping absolute value.
                #[inline]
                pub fn wrapping_abs(self) -> $Fixed<Frac> {
                    $Fixed::from_bits(<$Inner>::wrapping_abs(self.to_bits()))
                }
            }

            /// Overflowing negation.
            #[inline]
            pub fn overflowing_neg(self) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_neg(self.to_bits());
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point addition.
            #[inline]
            pub fn overflowing_add(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_add(self.to_bits(), rhs.to_bits());
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point subtraction.
            #[inline]
            pub fn overflowing_sub(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_sub(self.to_bits(), rhs.to_bits());
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point multiplication.
            #[inline]
            pub fn overflowing_mul(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::to_u32());
                ($Fixed::from_bits(ans), dir != Ordering::Equal)
            }

            /// Overflowing fixed-point division.
            #[inline]
            pub fn overflowing_div(self, rhs: $Fixed<Frac>) -> ($Fixed<Frac>, bool) {
                let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::to_u32());
                ($Fixed::from_bits(ans), dir != Ordering::Equal)
            }

            /// Overflowing fixed-point multiplication by integer.
            #[inline]
            pub fn overflowing_mul_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_mul(self.to_bits(), rhs);
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point division by integer.
            #[inline]
            pub fn overflowing_div_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_div(self.to_bits(), rhs);
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point remainder for division by integer.
            #[inline]
            pub fn overflowing_rem_int(self, rhs: $Inner) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_rem(self.to_bits(), rhs);
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point left shift.
            #[inline]
            pub fn overflowing_shl(self, rhs: u32) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_shl(self.to_bits(), rhs);
                ($Fixed::from_bits(ans), o)
            }

            /// Overflowing fixed-point right shift.
            #[inline]
            pub fn overflowing_shr(self, rhs: u32) -> ($Fixed<Frac>, bool) {
                let (ans, o) = <$Inner>::overflowing_shr(self.to_bits(), rhs);
                ($Fixed::from_bits(ans), o)
            }

            if_signed! {
                $Signedness =>
                /// Overflowing absolute value.
                #[inline]
                pub fn overflowing_abs(self) -> ($Fixed<Frac>, bool) {
                    let (ans, o) = <$Inner>::overflowing_abs(self.to_bits());
                    ($Fixed::from_bits(ans), o)
                }
            }

            if_unsigned! {
                $Signedness => pass_method! {
                    "Returns `true` if the fixed-point number is \
                     2<sup><i>k</i></sup> for some <i>k</i>.",
                    $Fixed($Inner) => fn is_power_of_two(self) -> bool
                }
            }

            if_unsigned! {
                $Signedness => pass_method! {
                    "Returns the smallest power of two ≥ `self`.",
                    $Fixed($Inner) => fn next_power_of_two(self)
                }
            }

            if_unsigned! {
                $Signedness =>
                /// Returns the smallest power of two ≥ `self`, or `None`
                /// if the next power of two is too large to represent.
                #[inline]
                pub fn checked_next_power_of_two(self) -> Option<$Fixed<Frac>> {
                    <$Inner>::checked_next_power_of_two(self.to_bits()).map($Fixed::from_bits)
                }
            }

            if_signed! {
                $Signedness => pass_method! {
                    "Returns the absolute value of two ≥ `self`.",
                    $Fixed($Inner) => fn abs(self)
                }
            }

            if_signed! {
                $Signedness =>
                /// Returns a number representing the sign of `self`.
                #[inline]
                pub fn signum(self) -> $Fixed<Frac> {
                    match self.to_bits().cmp(&0) {
                        Ordering::Equal => $Fixed::from_bits(0),
                        Ordering::Greater => {
                            <$Fixed<Frac> as FixedHelper<Frac>>::one().expect("overflow")
                        }
                        Ordering::Less => {
                            <$Fixed<Frac> as FixedHelper<Frac>>::minus_one().expect("overflow")
                        }
                    }
                }
            }
        }

        if_signed! {
            $Signedness => pass_one! { impl Neg for $Fixed($Inner) { neg } }
        }

        pass! { impl Add for $Fixed($Inner) { add } }
        pass_assign! { impl AddAssign for $Fixed($Inner) { add_assign } }
        pass! { impl Sub for $Fixed($Inner) { sub } }
        pass_assign! { impl SubAssign for $Fixed($Inner) { sub_assign } }

        impl<Frac: Unsigned> Mul<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, dir) = self.to_bits().mul_dir(rhs.to_bits(), Frac::to_u32());
                debug_assert!(dir == Ordering::Equal, "overflow");
                $Fixed::from_bits(ans)
            }
        }

        refs! { impl Mul for $Fixed($Inner) { mul } }

        impl<Frac: Unsigned> MulAssign<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn mul_assign(&mut self, rhs: $Fixed<Frac>) {
                *self = <$Fixed<Frac> as Mul<$Fixed<Frac>>>::mul(*self, rhs)
            }
        }

        refs_assign! { impl MulAssign for $Fixed($Inner) { mul_assign } }

        impl<Frac: Unsigned> Div<$Fixed<Frac>> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                let (ans, dir) = self.to_bits().div_dir(rhs.to_bits(), Frac::to_u32());
                debug_assert!(dir == Ordering::Equal, "overflow");
                $Fixed::from_bits(ans)
            }
        }

        refs! { impl Div for $Fixed($Inner) { div } }

        impl<Frac: Unsigned> DivAssign<$Fixed<Frac>> for $Fixed<Frac> {
            #[inline]
            fn div_assign(&mut self, rhs: $Fixed<Frac>) {
                *self = <$Fixed<Frac> as Div<$Fixed<Frac>>>::div(*self, rhs)
            }
        }

        refs_assign! { impl DivAssign for $Fixed($Inner) { div_assign } }

        pass_one! { impl Not for $Fixed($Inner) { not } }
        pass! { impl BitAnd for $Fixed($Inner) { bitand } }
        pass_assign! { impl BitAndAssign for $Fixed($Inner) { bitand_assign } }
        pass! { impl BitOr for $Fixed($Inner) { bitor } }
        pass_assign! { impl BitOrAssign for $Fixed($Inner) { bitor_assign } }
        pass! { impl BitXor for $Fixed($Inner) { bitxor } }
        pass_assign! { impl BitXorAssign for $Fixed($Inner) { bitxor_assign } }

        impl<Frac: Unsigned> Mul<$Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(self.to_bits() * rhs)
            }
        }

        impl<Frac: Unsigned> Mul<$Fixed<Frac>> for $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(rhs, self)
            }
        }

        impl<'a, Frac: Unsigned> Mul<$Inner> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> Mul<&'a $Fixed<Frac>> for $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(*rhs, self)
            }
        }

        impl<'a, Frac: Unsigned> Mul<&'a $Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(self, *rhs)
            }
        }

        impl<'a, Frac: Unsigned> Mul<$Fixed<Frac>> for &'a $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: $Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(rhs, *self)
            }
        }

        impl<'a, 'b, Frac: Unsigned> Mul<&'a $Inner> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(*self, *rhs)
            }
        }

        impl<'a, 'b, Frac: Unsigned> Mul<&'a $Fixed<Frac>> for &'b $Inner {
            type Output = $Fixed<Frac>;
            #[inline]
            fn mul(self, rhs: &$Fixed<Frac>) -> $Fixed<Frac> {
                <$Fixed<Frac> as Mul<$Inner>>::mul(*rhs, *self)
            }
        }

        impl<Frac: Unsigned> MulAssign<$Inner> for $Fixed<Frac> {
            #[inline]
            fn mul_assign(&mut self, rhs: $Inner) {
                *self = <$Fixed<Frac> as Mul<$Inner>>::mul(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> MulAssign<&'a $Inner> for $Fixed<Frac> {
            #[inline]
            fn mul_assign(&mut self, rhs: &$Inner) {
                *self = <$Fixed<Frac> as Mul<$Inner>>::mul(*self, *rhs)
            }
        }

        impl<Frac: Unsigned> Div<$Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(self.to_bits() / rhs)
            }
        }

        impl<'a, Frac: Unsigned> Div<$Inner> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: $Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Div<$Inner>>::div(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> Div<&'a $Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: &$Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Div<$Inner>>::div(self, *rhs)
            }
        }
        impl<'a, 'b, Frac: Unsigned> Div<&'a $Inner> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn div(self, rhs: &$Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Div<$Inner>>::div(*self, *rhs)
            }
        }

        impl<Frac: Unsigned> DivAssign<$Inner> for $Fixed<Frac> {
            #[inline]
            fn div_assign(&mut self, rhs: $Inner) {
                *self = <$Fixed<Frac> as Div<$Inner>>::div(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> DivAssign<&'a $Inner> for $Fixed<Frac> {
            #[inline]
            fn div_assign(&mut self, rhs: &$Inner) {
                *self = <$Fixed<Frac> as Div<$Inner>>::div(*self, *rhs)
            }
        }

        impl<Frac: Unsigned> Rem<$Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: $Inner) -> $Fixed<Frac> {
                $Fixed::from_bits(self.to_bits() % rhs)
            }
        }

        impl<'a, Frac: Unsigned> Rem<$Inner> for &'a $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: $Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Rem<$Inner>>::rem(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> Rem<&'a $Inner> for $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: &$Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Rem<$Inner>>::rem(self, *rhs)
            }
        }
        impl<'a, 'b, Frac: Unsigned> Rem<&'a $Inner> for &'b $Fixed<Frac> {
            type Output = $Fixed<Frac>;
            #[inline]
            fn rem(self, rhs: &$Inner) -> $Fixed<Frac> {
                <$Fixed<Frac> as Rem<$Inner>>::rem(*self, *rhs)
            }
        }

        impl<Frac: Unsigned> RemAssign<$Inner> for $Fixed<Frac> {
            #[inline]
            fn rem_assign(&mut self, rhs: $Inner) {
                *self = <$Fixed<Frac> as Rem<$Inner>>::rem(*self, rhs)
            }
        }

        impl<'a, Frac: Unsigned> RemAssign<&'a $Inner> for $Fixed<Frac> {
            #[inline]
            fn rem_assign(&mut self, rhs: &$Inner) {
                *self = <$Fixed<Frac> as Rem<$Inner>>::rem(*self, *rhs)
            }
        }

        shift_all! {
            impl {Shl, ShlAssign}<{
                i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
            }> for $Fixed($Inner) {
                shl, shl_assign
            }
        }
        shift_all! {
            impl {Shr, ShrAssign}<{
                i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
            }> for $Fixed($Inner) {
                shr, shr_assign
            }
        }

        impl<Frac: Unsigned> Sum<$Fixed<Frac>> for $Fixed<Frac> {
            fn sum<I: Iterator<Item = $Fixed<Frac>>>(iter: I) -> $Fixed<Frac> {
                iter.fold($Fixed::from_bits(0), Add::add)
            }
        }

        impl<'a, Frac: Unsigned + 'a> Sum<&'a $Fixed<Frac>> for $Fixed<Frac> {
            fn sum<I: Iterator<Item = &'a $Fixed<Frac>>>(iter: I) -> $Fixed<Frac> {
                iter.fold($Fixed::from_bits(0), Add::add)
            }
        }

        impl<Frac: Unsigned> Product<$Fixed<Frac>> for $Fixed<Frac> {
            fn product<I: Iterator<Item = $Fixed<Frac>>>(mut iter: I) -> $Fixed<Frac> {
                match iter.next() {
                    None => <$Fixed<Frac> as FixedHelper<Frac>>::one().expect("overflow"),
                    Some(first) => iter.fold(first, Mul::mul),
                }
            }
        }

        impl<'a, Frac: Unsigned + 'a> Product<&'a $Fixed<Frac>> for $Fixed<Frac> {
            fn product<I: Iterator<Item = &'a $Fixed<Frac>>>(mut iter: I) -> $Fixed<Frac> {
                match iter.next() {
                    None => <$Fixed<Frac> as FixedHelper<Frac>>::one().expect("overflow"),
                    Some(first) => iter.fold(*first, Mul::mul),
                }
            }
        }
    };
}

fixed! { "An eight-bit fixed-point unsigned integer", FixedU8(u8, 8), Unsigned }
fixed! { "A 16-bit fixed-point unsigned integer", FixedU16(u16, 16), Unsigned }
fixed! { "A 32-bit fixed-point unsigned integer", FixedU32(u32, 32), Unsigned }
fixed! { "A 64-bit fixed-point unsigned integer", FixedU64(u64, 64), Unsigned }
fixed! { "A 128-bit fixed-point unsigned integer", FixedU128(u128, 128), Unsigned }
fixed! { "An eight-bit fixed-point signed integer", FixedI8(i8, 8), Signed }
fixed! { "A 16-bit fixed-point signed integer", FixedI16(i16, 16), Signed }
fixed! { "A 32-bit fixed-point signed integer", FixedI32(i32, 32), Signed }
fixed! { "A 64-bit fixed-point signed integer", FixedI64(i64, 64), Signed }
fixed! { "A 128-bit fixed-point signed integer", FixedI128(i128, 128), Signed }

trait MulDivDir: Sized {
    fn mul_dir(self, rhs: Self, frac_bits: u32) -> (Self, Ordering);
    fn div_dir(self, rhs: Self, frac_bits: u32) -> (Self, Ordering);
}

macro_rules! mul_div_widen {
    ($Single:ty, $Double:ty, $Signedness:tt) => {
        impl MulDivDir for $Single {
            #[inline]
            fn mul_dir(self, rhs: $Single, frac_bits: u32) -> ($Single, Ordering) {
                const BITS: u32 = mem::size_of::<$Single>() as u32 * 8;
                let int_bits: u32 = BITS - frac_bits;
                let lhs2 = self as $Double;
                let rhs2 = rhs as $Double << int_bits;
                let (prod2, overflow) = lhs2.overflowing_mul(rhs2);
                let dir;
                if_unsigned! { $Signedness => {
                    dir = if !overflow {
                        Ordering::Equal
                    } else {
                        Ordering::Less
                    };
                } }
                if_signed! { $Signedness => {
                    dir = if !overflow {
                        Ordering::Equal
                    } else if (self < 0) == (rhs < 0) {
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    };
                } }
                ((prod2 >> BITS) as $Single, dir)
            }

            #[inline]
            fn div_dir(self, rhs: $Single, frac_bits: u32) -> ($Single, Ordering) {
                let lhs2 = self as $Double << frac_bits;
                let rhs2 = rhs as $Double;
                let quot2 = lhs2 / rhs2;
                let quot = quot2 as $Single;
                let dir = (quot as $Double).cmp(&quot2);
                (quot, dir)
            }
        }
    };
}

trait FallbackHelper: Sized {
    type Unsigned;
    fn hi_lo(self) -> (Self, Self);
    fn shift_lo_up(self) -> Self;
    fn shift_lo_up_unsigned(self) -> Self::Unsigned;
    fn combine_lo_then_shl(self, lo: Self::Unsigned, shift: u32) -> (Self, Ordering);
    fn carrying_add(self, other: Self) -> (Self, Self);
}

impl FallbackHelper for u128 {
    type Unsigned = u128;
    #[inline]
    fn hi_lo(self) -> (u128, u128) {
        (self >> 64, self & !(!0 << 64))
    }

    #[inline]
    fn shift_lo_up(self) -> u128 {
        debug_assert!(self >> 64 == 0);
        self << 64
    }

    #[inline]
    fn shift_lo_up_unsigned(self) -> u128 {
        debug_assert!(self >> 64 == 0);
        self << 64
    }

    #[inline]
    fn combine_lo_then_shl(self, lo: u128, shift: u32) -> (u128, Ordering) {
        if shift == 128 {
            return (self, Ordering::Equal);
        }
        if shift == 0 {
            return (lo, 0.cmp(&self));
        }
        let lo = lo >> shift;
        let hi = self << (128 - shift);
        (lo | hi, 0.cmp(&(self >> shift)))
    }

    #[inline]
    fn carrying_add(self, rhs: u128) -> (u128, u128) {
        let (sum, overflow) = self.overflowing_add(rhs);
        let carry = if overflow { 1 } else { 0 };
        (sum, carry)
    }
}

impl FallbackHelper for i128 {
    type Unsigned = u128;
    #[inline]
    fn hi_lo(self) -> (i128, i128) {
        (self >> 64, self & !(!0 << 64))
    }

    #[inline]
    fn shift_lo_up(self) -> i128 {
        debug_assert!(self >> 64 == 0);
        self << 64
    }

    #[inline]
    fn shift_lo_up_unsigned(self) -> u128 {
        debug_assert!(self >> 64 == 0);
        (self << 64) as u128
    }

    #[inline]
    fn combine_lo_then_shl(self, lo: u128, shift: u32) -> (i128, Ordering) {
        if shift == 128 {
            return (self, Ordering::Equal);
        }
        if shift == 0 {
            let ans = lo as i128;
            return (ans, (ans >> 64 >> 64).cmp(&self));
        }
        let lo = (lo >> shift) as i128;
        let hi = self << (128 - shift);
        let ans = lo | hi;
        (ans, (ans >> 64 >> 64).cmp(&(self >> shift)))
    }

    #[inline]
    fn carrying_add(self, rhs: i128) -> (i128, i128) {
        let (sum, overflow) = self.overflowing_add(rhs);
        let carry = if overflow {
            if sum < 0 {
                1
            } else {
                -1
            }
        } else {
            0
        };
        (sum, carry)
    }
}

macro_rules! mul_div_fallback {
    ($Single:ty, $Signedness:tt) => {
        impl MulDivDir for $Single {
            fn mul_dir(self, rhs: $Single, frac_bits: u32) -> ($Single, Ordering) {
                if frac_bits == 0 {
                    let (ans, overflow) = self.overflowing_mul(rhs);
                    let dir;
                    if_unsigned! { $Signedness => {
                        dir = if !overflow {
                            Ordering::Equal
                        } else {
                            Ordering::Less
                        };
                    } }
                    if_signed! { $Signedness => {
                        dir = if !overflow {
                            Ordering::Equal
                        } else if (self < 0) == (rhs < 0) {
                            Ordering::Less
                        } else {
                            Ordering::Greater
                        };
                    } }
                    (ans, dir)
                } else {
                    let (lh, ll) = self.hi_lo();
                    let (rh, rl) = rhs.hi_lo();
                    let ll_rl = ll.wrapping_mul(rl);
                    let lh_rl = lh.wrapping_mul(rl);
                    let ll_rh = ll.wrapping_mul(rh);
                    let lh_rh = lh.wrapping_mul(rh);
                    let col01 = ll_rl as <$Single as FallbackHelper>::Unsigned;
                    let (col12, carry_col3) = lh_rl.carrying_add(ll_rh);
                    let col23 = lh_rh;
                    let (col12_hi, col12_lo) = col12.hi_lo();
                    let col12_lo_up = col12_lo.shift_lo_up_unsigned();
                    let (ans01, carry_col2) = col01.carrying_add(col12_lo_up);
                    let carries = carry_col2 as $Single + carry_col3.shift_lo_up();
                    let ans23 = col23.wrapping_add(carries).wrapping_add(col12_hi);

                    ans23.combine_lo_then_shl(ans01, frac_bits)
                }
            }

            fn div_dir(self, rhs: $Single, frac_bits: u32) -> ($Single, Ordering) {
                if frac_bits == 0 {
                    let (ans, overflow) = self.overflowing_div(rhs);
                    let dir;
                    if_unsigned! { $Signedness => {
                        dir = if !overflow {
                            Ordering::Equal
                        } else {
                            Ordering::Less
                        };
                    } }
                    if_signed! { $Signedness => {
                        dir = if !overflow {
                            Ordering::Equal
                        } else if (self < 0) == (rhs < 0) {
                            Ordering::Less
                        } else {
                            Ordering::Greater
                        };
                    } }
                    (ans, dir)
                } else {
                    unimplemented!()
                }
            }
        }
    };
}

mul_div_widen! { u8, u16, Unsigned }
mul_div_widen! { u16, u32, Unsigned }
mul_div_widen! { u32, u64, Unsigned }
mul_div_widen! { u64, u128, Unsigned }
mul_div_fallback! { u128, Unsigned }
mul_div_widen! { i8, i16, Signed }
mul_div_widen! { i16, i32, Signed }
mul_div_widen! { i32, i64, Signed }
mul_div_widen! { i64, i128, Signed }
mul_div_fallback! { i128, Signed }

#[cfg(test)]
mod tests {
    use *;

    #[test]
    fn fixed_u16() {
        use frac::U7 as Frac;
        let frac = Frac::to_u32();
        let a = 12;
        let b = 4;
        let af = FixedU16::<Frac>::from_bits(a << Frac::to_u32());
        let bf = FixedU16::<Frac>::from_bits(b << Frac::to_u32());
        assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
        assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
        assert_eq!((af * bf).to_bits(), (a << frac) * b);
        assert_eq!((af / bf).to_bits(), (a << frac) / b);
        assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
        assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
        assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
        assert_eq!((!af).to_bits(), !(a << frac));
        assert_eq!((af << 4u8).to_bits(), (a << frac) << 4);
        assert_eq!((af >> 4i128).to_bits(), (a << frac) >> 4);
    }

    #[test]
    fn fixed_i16() {
        use frac::U7 as Frac;
        let frac = Frac::to_u32();
        let a = 12;
        let b = 4;
        for &pair in &[(a, b), (a, -b), (-a, b), (-a, -b)] {
            let (a, b) = pair;
            let af = FixedI16::<Frac>::from_bits(a << frac);
            let bf = FixedI16::<Frac>::from_bits(b << frac);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((-af).to_bits(), -(a << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
            assert_eq!((af << 4u8).to_bits(), (a << frac) << 4);
            assert_eq!((af >> 4i128).to_bits(), (a << frac) >> 4);
        }
    }

    #[test]
    fn fixed_u128() {
        use frac::U7 as Frac;
        let frac = Frac::to_u32();
        let a = 0x0003456789abcdef_0123456789abcdef_u128;
        let b = 5;
        let af = FixedU128::<Frac>::from_bits(a << frac);
        let bf = FixedU128::<Frac>::from_bits(b << frac);
        assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
        assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
        assert_eq!((af * bf).to_bits(), (a << frac) * b);
        // assert_eq!((af / bf).to_bits(), (a << frac) / b);
        assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
        assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
        assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
        assert_eq!((!af).to_bits(), !(a << frac));
    }

    #[test]
    fn fixed_i128() {
        use frac::U7 as Frac;
        let frac = Frac::to_u32();
        let a = 0x0003456789abcdef_0123456789abcdef_i128;
        let b = 5;
        for &pair in &[(a, b), (a, -b), (-a, b), (-a, -b)] {
            let (a, b) = pair;
            let af = FixedI128::<Frac>::from_bits(a << frac);
            let bf = FixedI128::<Frac>::from_bits(b << frac);
            assert_eq!((af + bf).to_bits(), (a << frac) + (b << frac));
            assert_eq!((af - bf).to_bits(), (a << frac) - (b << frac));
            assert_eq!((af * bf).to_bits(), (a << frac) * b);
            // assert_eq!((af / bf).to_bits(), (a << frac) / b);
            assert_eq!((af & bf).to_bits(), (a << frac) & (b << frac));
            assert_eq!((af | bf).to_bits(), (a << frac) | (b << frac));
            assert_eq!((af ^ bf).to_bits(), (a << frac) ^ (b << frac));
            assert_eq!((!af).to_bits(), !(a << frac));
        }
    }

    #[test]
    fn to_f32() {
        use frac::U7 as Frac;
        for u in 0x00..=0xff {
            let fu = FixedU8::<Frac>::from_bits(u);
            assert_eq!(fu.to_f32(), u as f32 / 128.0);
            let i = u as i8;
            let fi = FixedI8::<Frac>::from_bits(i);
            assert_eq!(fi.to_f32(), i as f32 / 128.0);

            for hi in &[
                0u32,
                0x0000_0100,
                0x7fff_ff00,
                0x8000_0000,
                0x8100_0000,
                0xffff_fe00,
                0xffff_ff00,
            ] {
                let uu = *hi | u as u32;
                let fuu = FixedU32::<Frac>::from_bits(uu);
                assert_eq!(fuu.to_f32(), uu as f32 / 128.0);
                let ii = uu as i32;
                let fii = FixedI32::<Frac>::from_bits(ii);
                assert_eq!(fii.to_f32(), ii as f32 / 128.0);
            }

            for hi in &[
                0u128,
                0x0000_0000_0000_0000_0000_0000_0000_0100,
                0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
                0x8000_0000_0000_0000_0000_0000_0000_0000,
                0x8100_0000_0000_0000_0000_0000_0000_0000,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fe00,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
            ] {
                let uu = *hi | u as u128;
                let fuu = FixedU128::<Frac>::from_bits(uu);
                assert_eq!(fuu.to_f32(), (uu as f64 / 128.0) as f32);
                let ii = uu as i128;
                let fii = FixedI128::<Frac>::from_bits(ii);
                assert_eq!(fii.to_f32(), (ii as f64 / 128.0) as f32);
            }
        }
    }

    #[test]
    fn to_f64() {
        use frac::U7 as Frac;
        for u in 0x00..=0xff {
            let fu = FixedU8::<Frac>::from_bits(u);
            assert_eq!(fu.to_f32(), u as f32 / 128.0);
            let i = u as i8;
            let fi = FixedI8::<Frac>::from_bits(i);
            assert_eq!(fi.to_f32(), i as f32 / 128.0);

            for hi in &[
                0u64,
                0x0000_0000_0000_0100,
                0x7fff_ffff_ffff_ff00,
                0x8000_0000_0000_0000,
                0x8100_0000_0000_0000,
                0xffff_ffff_ffff_fe00,
                0xffff_ffff_ffff_ff00,
            ] {
                let uu = *hi | u as u64;
                let fuu = FixedU64::<Frac>::from_bits(uu);
                assert_eq!(fuu.to_f64(), uu as f64 / 128.0);
                let ii = uu as i64;
                let fii = FixedI64::<Frac>::from_bits(ii);
                assert_eq!(fii.to_f64(), ii as f64 / 128.0);
            }

            for hi in &[
                0u128,
                0x0000_0000_0000_0000_0000_0000_0000_0100,
                0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
                0x8000_0000_0000_0000_0000_0000_0000_0000,
                0x8100_0000_0000_0000_0000_0000_0000_0000,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fe00,
                0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ff00,
            ] {
                let uu = *hi | u as u128;
                let fuu = FixedU128::<Frac>::from_bits(uu);
                assert_eq!(fuu.to_f64(), uu as f64 / 128.0);
                let ii = uu as i128;
                let fii = FixedI128::<Frac>::from_bits(ii);
                assert_eq!(fii.to_f64(), ii as f64 / 128.0);
            }
        }
    }

    #[test]
    fn rounding() {
        use typenum::{U16, U32};

        type I0F32 = FixedI32<U32>;

        // -0.5
        let f = I0F32::from_bits(-1 << 31);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), -1);

        // -0.5 + δ
        let f = I0F32::from_bits((-1 << 31) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), 0);

        // 0.5 - δ
        let f = I0F32::from_bits((1 << 30) - 1 + (1 << 30));
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 0);

        type U0F32 = FixedU32<U32>;

        // 0.5 - δ
        let f = U0F32::from_bits((1 << 31) - 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 0);

        // 0.5
        let f = U0F32::from_bits(1 << 31);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);

        // 0.5 + δ
        let f = U0F32::from_bits((1 << 31) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);

        type I16F16 = FixedI32<U16>;

        // -3.5 - δ
        let f = I16F16::from_bits(((-7) << 15) - 1);
        assert_eq!(f.to_int(), -3);
        assert_eq!(f.to_int_ceil(), -3);
        assert_eq!(f.to_int_floor(), -4);
        assert_eq!(f.to_int_round(), -4);

        // -3.5
        let f = I16F16::from_bits((-7) << 15);
        assert_eq!(f.to_int(), -3);
        assert_eq!(f.to_int_ceil(), -3);
        assert_eq!(f.to_int_floor(), -4);
        assert_eq!(f.to_int_round(), -4);

        // -3.5 + δ
        let f = I16F16::from_bits(((-7) << 15) + 1);
        assert_eq!(f.to_int(), -3);
        assert_eq!(f.to_int_ceil(), -3);
        assert_eq!(f.to_int_floor(), -4);
        assert_eq!(f.to_int_round(), -3);

        // -0.5 - δ
        let f = I16F16::from_bits(((-1) << 15) - 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), -1);

        // -0.5
        let f = I16F16::from_bits((-1) << 15);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), -1);

        // -0.5 + δ
        let f = I16F16::from_bits(((-1) << 15) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 0);
        assert_eq!(f.to_int_floor(), -1);
        assert_eq!(f.to_int_round(), 0);

        // 0.5 - δ
        let f = I16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 0);

        // 0.5
        let f = I16F16::from_bits(1 << 15);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);

        // 0.5 + δ
        let f = I16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);

        // 3.5 - δ
        let f = I16F16::from_bits((7 << 15) - 1);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 3);

        // 3.5
        let f = I16F16::from_bits(7 << 15);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 4);

        // 3.5 + δ
        let f = I16F16::from_bits((7 << 15) + 1);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 4);

        type U16F16 = FixedU32<U16>;

        // 0.5 - δ
        let f = U16F16::from_bits((1 << 15) - 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 0);

        // 0.5
        let f = U16F16::from_bits(1 << 15);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);

        // 0.5 + δ
        let f = U16F16::from_bits((1 << 15) + 1);
        assert_eq!(f.to_int(), 0);
        assert_eq!(f.to_int_ceil(), 1);
        assert_eq!(f.to_int_floor(), 0);
        assert_eq!(f.to_int_round(), 1);

        // 3.5 - δ
        let f = U16F16::from_bits((7 << 15) - 1);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 3);

        // 3.5
        let f = U16F16::from_bits(7 << 15);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 4);

        // 3.5 + δ
        let f = U16F16::from_bits((7 << 15) + 1);
        assert_eq!(f.to_int(), 3);
        assert_eq!(f.to_int_ceil(), 4);
        assert_eq!(f.to_int_floor(), 3);
        assert_eq!(f.to_int_round(), 4);
    }
}
