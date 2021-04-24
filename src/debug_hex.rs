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
    sync::atomic::{AtomicU32, Ordering},
};

// This is an ugly hack to check whether a `Formatter` has `debug_lower_hex` or
// `debug_upper_hex`.
//
// For `is_debug_lower_hex`, we do a dummy write with format string "{:x?}",
// then get the flags using the deprecated `Formatter::flags`. There should be
// one set bit in the returned flags, which is cached inside `DEBUG_LOWER_HEX`.
// The obtained flag mask is then used to test the flags from the formatter
// under test.
//
// If something fails, `u32::MAX` is stored in `DEBUG_LOWER_HEX` to avoid
// repeating the dummy write.
//
// A similar process is used for `is_debug_upper_hex` with a format string
// "{:X?}" used for the dummy write.

// Both `DEBUG_LOWER_HEX` and `DEBUG_UPPER_HEX` are:
//   * 0 for not cached
//   * `u32::MAX` for error
//   * otherwise a single bit mask
static DEBUG_LOWER_HEX: AtomicU32 = AtomicU32::new(0);
static DEBUG_UPPER_HEX: AtomicU32 = AtomicU32::new(0);

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

fn is_debug_hex(
    f: &Formatter,
    cache: &AtomicU32,
    obtain_flags: fn(store_flags: &StoreFlags) -> FmtResult,
) -> bool {
    let flags = get_flags(f);
    if flags == 0 {
        return false;
    }
    let mut flag_mask = cache.load(Ordering::Relaxed);
    if flag_mask == u32::MAX {
        return false;
    }
    if flag_mask == 0 {
        let store_flags = StoreFlags(Cell::new(0));
        if obtain_flags(&store_flags).is_err() {
            cache.store(u32::MAX, Ordering::Relaxed);
            return false;
        }
        flag_mask = store_flags.0.get();
        if flag_mask.count_ones() != 1 {
            cache.store(u32::MAX, Ordering::Relaxed);
            return false;
        }
        cache.store(flag_mask, Ordering::Relaxed);
    }
    (flags & flag_mask) != 0
}

fn obtain_flags_lower(store_flags: &StoreFlags) -> FmtResult {
    write!(Discard, "{:x?}", store_flags)
}

fn obtain_flags_upper(store_flags: &StoreFlags) -> FmtResult {
    write!(Discard, "{:X?}", store_flags)
}

pub fn is_debug_lower_hex(f: &Formatter) -> bool {
    is_debug_hex(f, &DEBUG_LOWER_HEX, obtain_flags_lower)
}

pub fn is_debug_upper_hex(f: &Formatter) -> bool {
    is_debug_hex(f, &DEBUG_UPPER_HEX, obtain_flags_upper)
}
