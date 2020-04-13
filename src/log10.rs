// Copyright © 2018–2019 Trevor Spiteri

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

// self must be positive
pub trait IntFracLog10 {
    fn int_part_log10(self) -> i32;
    fn frac_part_log10(self) -> i32;
}

impl IntFracLog10 for u8 {
    #[inline]
    fn int_part_log10(self) -> i32 {
        if self >= 100 {
            2
        } else if self >= 10 {
            1
        } else {
            debug_assert!(self >= 1);
            0
        }
    }

    #[inline]
    fn frac_part_log10(self) -> i32 {
        if self > 25 {
            -1
        } else if self > 2 {
            -2
        } else {
            debug_assert!(self > 0);
            -3
        }
    }
}

impl IntFracLog10 for u16 {
    #[inline]
    fn int_part_log10(self) -> i32 {
        if self >= 10_000 {
            4
        } else if self >= 1000 {
            3
        } else if self >= 100 {
            2
        } else if self >= 10 {
            1
        } else {
            debug_assert!(self >= 1);
            0
        }
    }

    #[inline]
    fn frac_part_log10(self) -> i32 {
        if self > 6553 {
            -1
        } else if self > 655 {
            -2
        } else if self > 65 {
            -3
        } else if self > 6 {
            -4
        } else {
            debug_assert!(self > 0);
            -5
        }
    }
}

fn int_part_log10_less_than_8(mut i: u32) -> i32 {
    debug_assert!(i < 100_000_000);
    let mut log = 0;
    if i >= 10_000 {
        i /= 10_000;
        log += 4;
    }
    log + if i >= 1000 {
        3
    } else if i >= 100 {
        2
    } else if i >= 10 {
        1
    } else {
        debug_assert!(i >= 1);
        0
    }
}

fn frac_part_log10_greater_equal_m8(mut i: u32) -> i32 {
    const MAX: u32 = u32::max_value();
    debug_assert!(i > MAX / 100_000_000);
    let mut log = 0;
    if i <= MAX / 10_000 {
        i *= 10_000;
        log += -4;
    }
    log + if i > MAX / 10 {
        -1
    } else if i > MAX / 100 {
        -2
    } else if i > MAX / 1000 {
        -3
    } else {
        debug_assert!(i > MAX / 10_000);
        -4
    }
}

impl IntFracLog10 for u32 {
    fn int_part_log10(mut self) -> i32 {
        let mut log = 0;
        if self >= 100_000_000 {
            self /= 100_000_000;
            log += 8;
        }
        log + int_part_log10_less_than_8(self)
    }

    fn frac_part_log10(mut self) -> i32 {
        const MAX: u32 = u32::max_value();
        let mut log = 0;
        if self <= MAX / 100_000_000 {
            self *= 100_000_000;
            log += -8;
        }
        log + frac_part_log10_greater_equal_m8(self)
    }
}

fn int_part_log10_less_than_16(mut i: u64) -> i32 {
    debug_assert!(i < 10_000_000_000_000_000);
    let mut log = 0;
    if i >= 100_000_000 {
        i /= 100_000_000;
        log += 8;
    }
    debug_assert_eq!(i >> 32, 0);
    log + int_part_log10_less_than_8(i as u32)
}

// This is only used by u128::frac_part_log10, not by
// u64::frac_part_log10 where we can actually skip the two initial
// comparisons when we already have log = -16.
fn frac_part_log10_greater_equal_m16(mut i: u64) -> i32 {
    const MAX: u64 = u64::max_value();
    debug_assert!(i > MAX / 10_000_000_000_000_000);
    let mut log = 0;
    if i <= MAX / 100_000_000 {
        i *= 100_000_000;
        log += -8;
    }
    if i <= MAX / 10_000 {
        i *= 10_000;
        log += -4;
    }
    log + if i > MAX / 10 {
        -1
    } else if i > MAX / 100 {
        -2
    } else if i > MAX / 1000 {
        -3
    } else {
        debug_assert!(i > MAX / 10_000);
        -4
    }
}

impl IntFracLog10 for u64 {
    fn int_part_log10(mut self) -> i32 {
        let mut log = 0;
        if self >= 10_000_000_000_000_000 {
            self /= 10_000_000_000_000_000;
            log += 16;
        }
        log + int_part_log10_less_than_16(self)
    }

    fn frac_part_log10(mut self) -> i32 {
        const MAX: u64 = u64::max_value();
        let mut log = 0;
        if self <= MAX / 10_000_000_000_000_000 {
            // After this, self >= 10^16 > MAX / 10^4 == 1.84 × 10^15.
            self *= 10_000_000_000_000_000;
            log += -16;
        } else {
            if self <= MAX / 100_000_000 {
                self *= 100_000_000;
                log += -8;
            }
            if self <= MAX / 10_000 {
                self *= 10_000;
                log += -4;
            }
        }
        log + if self > MAX / 10 {
            -1
        } else if self > MAX / 100 {
            -2
        } else if self > MAX / 1000 {
            -3
        } else {
            debug_assert!(self > MAX / 10_000);
            -4
        }
    }
}

impl IntFracLog10 for u128 {
    fn int_part_log10(mut self) -> i32 {
        let mut log = 0;
        if self >= 100_000_000_000_000_000_000_000_000_000_000 {
            self /= 100_000_000_000_000_000_000_000_000_000_000;
            log += 32;
            debug_assert_eq!(self >> 32, 0);
            return log + int_part_log10_less_than_8(self as u32);
        }
        if self >= 10_000_000_000_000_000 {
            self /= 10_000_000_000_000_000;
            log += 16;
        }
        debug_assert_eq!(self >> 64, 0);
        log + int_part_log10_less_than_16(self as u64)
    }

    fn frac_part_log10(mut self) -> i32 {
        const MAX: u128 = u128::max_value();
        let mut log = 0;
        if self <= MAX / 100_000_000_000_000_000_000_000_000_000_000 {
            self *= 100_000_000_000_000_000_000_000_000_000_000;
            log += -32;
            // At this point  we have shifted out 32 digits, and we can only shift out 7 more.
            return log + frac_part_log10_greater_equal_m8((self >> 96) as u32);
        }
        if self <= MAX / 10_000_000_000_000_000 {
            self *= 10_000_000_000_000_000;
            log += -16;
        }
        if self <= MAX / 100_000_000 {
            self *= 100_000_000;
            log += -8;
        }
        if log <= -24 {
            // At this point  we have shifted out 24 digits, and we can only shift out 15 more.
            return log + frac_part_log10_greater_equal_m16((self >> 64) as u64);
        }
        if self <= MAX / 10_000 {
            self *= 10_000;
            log += -4;
        }
        log + if self > MAX / 10 {
            -1
        } else if self > MAX / 100 {
            -2
        } else if self > MAX / 1000 {
            -3
        } else {
            debug_assert!(self > MAX / 10_000);
            -4
        }
    }
}

#[cfg(test)]
mod tests {
    use super::IntFracLog10;

    macro_rules! check_loop {
        ($T:ty, $max:expr, $min:expr) => {
            assert_eq!(<$T>::max_value().int_part_log10(), $max);
            for i in 0..=$max {
                let p = (10 as $T).pow(i as u32);
                if i > 0 {
                    assert_eq!((p - 1).int_part_log10(), i - 1);
                }
                assert_eq!(p.int_part_log10(), i);
                assert_eq!((p + 1).int_part_log10(), i);
            }

            assert_eq!((1 as $T).frac_part_log10(), $min);
            for i in 0..-$min {
                let p = <$T>::max_value() / (10 as $T).pow(i as u32);
                if p > 1 {
                    assert_eq!((p - 1).frac_part_log10(), -1 - i);
                }
                assert_eq!(p.frac_part_log10(), -1 - i);
                if i > 0 {
                    assert_eq!((p + 1).frac_part_log10(), -i);
                }
            }
        };
    }

    #[test]
    fn log10_u8() {
        check_loop! { u8, 2, -3 }
    }

    #[test]
    fn log10_u16() {
        check_loop! { u16, 4, -5 }
    }

    #[test]
    fn log10_u32() {
        check_loop! { u32, 9, -10 }
    }

    #[test]
    fn log10_u64() {
        check_loop! { u64, 19, -20 }
    }

    #[test]
    fn log10_u128() {
        check_loop! { u128, 38, -39 }
    }
}
