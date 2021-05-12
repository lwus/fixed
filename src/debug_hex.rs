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

use core::{
    cell::Cell,
    fmt::{Debug, Formatter, Result as FmtResult, Write},
    sync::atomic::{AtomicU64, Ordering},
};

// This is an ugly hack to check whether a `Formatter` has `debug_lower_hex` or
// `debug_upper_hex`.
//
// We do a dummy write with format string "{:x?}" to get `debug_lower_hex`, and
// a dummy write with format string "{:X?}" to get `debug_upper_hex`. Each time,
// we get the flags using the deprecated `Formatter::flags`. There should be one
// set bit in each that is cleared in the other. These bits are the masks for
// lower and upper hex. We store them inside `DEBUG_HEX_MASKS`.
//
// If something fails, `u64::MAX` is stored in `DEBUG_HEX_MASKS` to avoid
// repeating the dummy write.

// `DEBUG_HEX_MASKS` is:
//   * 0 for not cached
//   * `u64::MAX` for error
//   * otherwise a `u64` with `debug_lower_hex` as the lower 32 bits and
//     `debug_upper_hex` as the higher 32 bits. Both should have one bit set.
static DEBUG_HEX_MASKS: AtomicU64 = AtomicU64::new(0);

fn get_flags(f: &Formatter) -> u32 {
    #[allow(deprecated)]
    f.flags()
}

struct StoreFlags(Cell<u32>);

impl Debug for StoreFlags {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        self.0.set(get_flags(f));
        Ok(())
    }
}

struct Discard;

impl Write for Discard {
    fn write_str(&mut self, _s: &str) -> FmtResult {
        Ok(())
    }
}

pub enum IsDebugHex {
    Lower,
    Upper,
    No,
}

pub fn is_debug_hex(f: &Formatter) -> IsDebugHex {
    let flags = get_flags(f);
    // avoid doing unnecessary work if flags is zero get_low
    if flags == 0 {
        return IsDebugHex::No;
    }
    let (lower, upper) = get_lower_upper_masks();
    if flags & lower != 0 {
        IsDebugHex::Lower
    } else if flags & upper != 0 {
        IsDebugHex::Upper
    } else {
        IsDebugHex::No
    }
}

fn get_lower_upper_masks() -> (u32, u32) {
    let masks = DEBUG_HEX_MASKS.load(Ordering::Relaxed);
    if masks == u64::MAX {
        return (0, 0);
    }
    if masks != 0 {
        return (masks as u32, (masks >> 32) as u32);
    }

    match determine_masks() {
        None => {
            DEBUG_HEX_MASKS.store(u64::MAX, Ordering::Relaxed);
            (0, 0)
        }
        Some((lower, upper)) => {
            let masks = (lower as u64) | ((upper as u64) << 32);
            DEBUG_HEX_MASKS.store(masks, Ordering::Relaxed);
            (lower, upper)
        }
    }
}

fn determine_masks() -> Option<(u32, u32)> {
    let store_flags = StoreFlags(Cell::new(0));
    write!(Discard, "{:x?}", store_flags).ok()?;
    let lower_flags = store_flags.0.get();
    write!(Discard, "{:X?}", store_flags).ok()?;
    let upper_flags = store_flags.0.get();
    let lower_mask = lower_flags & !upper_flags;
    let upper_mask = upper_flags & !lower_flags;
    if lower_mask.count_ones() != 1 || upper_mask.count_ones() != 1 {
        return None;
    }
    Some((lower_mask, upper_mask))
}
