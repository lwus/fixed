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

#[cfg(feature = "unwrapped")]
use crate::Unwrapped;
use crate::{
    types::extra::{LeEqU128, LeEqU16, LeEqU32, LeEqU64, LeEqU8},
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8, Wrapping,
};
use core::{
    fmt::{Error as FmtError, Formatter, Result as FmtResult, Write as FmtWrite},
    marker::PhantomData,
    str,
};
use serde::{
    de::{self, Deserialize, Deserializer, MapAccess, SeqAccess, Unexpected, Visitor},
    ser::{Serialize, SerializeStruct, Serializer},
};

// 42 bytes should be approximately enough for FixedI128:
//   * log_10(2^128) == 39
//   * one each for: sign, period, zero in case of I0F128
// To be safe and not care about corner cases, we just use 48 bytes.
struct Buffer {
    len: usize,
    data: [u8; 48],
}

impl FmtWrite for Buffer {
    fn write_str(&mut self, s: &str) -> Result<(), FmtError> {
        let next_len = self.len + s.len();
        self.data[self.len..next_len].copy_from_slice(s.as_bytes());
        self.len = next_len;
        Ok(())
    }
}

macro_rules! serde_fixed {
    ($Fixed:ident($LeEqU:ident) is $TBits:ident name $Name:expr) => {
        impl<Frac: $LeEqU> Serialize for $Fixed<Frac> {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                let is_human_readable = serializer.is_human_readable();
                let mut state = serializer.serialize_struct($Name, 1)?;
                if cfg!(feature = "serde-str") && is_human_readable {
                    let mut buffer = Buffer {
                        len: 0,
                        data: [0; 48],
                    };
                    let _ = write!(buffer, "{}", self);
                    let string = str::from_utf8(&buffer.data[0..buffer.len]).expect("utf8");
                    state.serialize_field("value", string)?;
                } else {
                    let bits = self.to_bits();
                    state.serialize_field("bits", &bits)?;
                }
                state.end()
            }
        }

        impl<Frac: $LeEqU> Serialize for Wrapping<$Fixed<Frac>> {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                self.0.serialize(serializer)
            }
        }

        #[cfg(feature = "unwrapped")]
        impl<Frac: $LeEqU> Serialize for Unwrapped<$Fixed<Frac>> {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                self.0.serialize(serializer)
            }
        }

        impl<'de, Frac: $LeEqU> Deserialize<'de> for $Fixed<Frac> {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                struct FixedVisitor<Frac: $LeEqU> {
                    phantom: PhantomData<Frac>,
                    is_human_readable: bool,
                };

                impl<'de, Frac: $LeEqU> Visitor<'de> for FixedVisitor<Frac> {
                    type Value = $TBits;

                    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
                        formatter.write_str("struct ")?;
                        formatter.write_str($Name)
                    }

                    fn visit_seq<V: SeqAccess<'de>>(self, mut seq: V) -> Result<$TBits, V::Error> {
                        if cfg!(feature = "serde-str") && self.is_human_readable {
                            let string: &str = seq
                                .next_element()?
                                .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                            let num: $Fixed<Frac> = string.parse().map_err(|_| {
                                de::Error::invalid_value(Unexpected::Str(string), &self)
                            })?;
                            Ok(num.to_bits())
                        } else {
                            let bits = seq
                                .next_element()?
                                .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                            Ok(bits)
                        }
                    }

                    #[cfg(not(feature = "serde-str"))]
                    fn visit_map<V: MapAccess<'de>>(self, mut map: V) -> Result<$TBits, V::Error> {
                        let mut bits = None;
                        while let Some(key) = map.next_key()? {
                            match key {
                                Field::Bits => {
                                    if bits.is_some() {
                                        return Err(de::Error::duplicate_field("bits"));
                                    }
                                    bits = Some(map.next_value()?);
                                }
                            }
                        }
                        let bits = bits.ok_or_else(|| de::Error::missing_field("bits"))?;
                        Ok(bits)
                    }

                    #[cfg(feature = "serde-str")]
                    fn visit_map<V: MapAccess<'de>>(self, mut map: V) -> Result<$TBits, V::Error> {
                        let mut bits = None;
                        while let Some(key) = map.next_key()? {
                            match key {
                                Field::Bits => {
                                    if bits.is_some() {
                                        return Err(de::Error::duplicate_field("bits"));
                                    }
                                    bits = Some(map.next_value()?);
                                }
                                Field::Value => {
                                    if bits.is_some() {
                                        return Err(de::Error::duplicate_field("value"));
                                    }
                                    let string: &str = map.next_value()?;
                                    let num: $Fixed<Frac> = string.parse().map_err(|_| {
                                        de::Error::invalid_value(Unexpected::Str(string), &self)
                                    })?;
                                    bits = Some(num.to_bits());
                                }
                            }
                        }
                        let bits = bits.ok_or_else(|| de::Error::missing_field("value"))?;
                        Ok(bits)
                    }
                }

                let is_human_readable = deserializer.is_human_readable();
                let bits = deserializer.deserialize_struct(
                    $Name,
                    FIELDS,
                    FixedVisitor::<Frac> {
                        phantom: PhantomData,
                        is_human_readable,
                    },
                )?;
                Ok($Fixed::from_bits(bits))
            }
        }

        impl<'de, Frac: $LeEqU> Deserialize<'de> for Wrapping<$Fixed<Frac>> {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                $Fixed::deserialize(deserializer).map(Wrapping)
            }
        }

        #[cfg(feature = "unwrapped")]
        impl<'de, Frac: $LeEqU> Deserialize<'de> for Unwrapped<$Fixed<Frac>> {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                $Fixed::deserialize(deserializer).map(Unwrapped)
            }
        }
    };
}

serde_fixed! { FixedI8(LeEqU8) is i8 name "FixedI8" }
serde_fixed! { FixedI16(LeEqU16) is i16 name "FixedI16" }
serde_fixed! { FixedI32(LeEqU32) is i32 name "FixedI32" }
serde_fixed! { FixedI64(LeEqU64) is i64 name "FixedI64" }
serde_fixed! { FixedI128(LeEqU128) is i128 name "FixedI128" }
serde_fixed! { FixedU8(LeEqU8) is u8 name "FixedU8" }
serde_fixed! { FixedU16(LeEqU16) is u16 name "FixedU16" }
serde_fixed! { FixedU32(LeEqU32) is u32 name "FixedU32" }
serde_fixed! { FixedU64(LeEqU64) is u64 name "FixedU64" }
serde_fixed! { FixedU128(LeEqU128) is u128 name "FixedU128" }

#[cfg(not(feature = "serde-str"))]
const FIELDS: &[&str] = &["bits"];
#[cfg(feature = "serde-str")]
const FIELDS: &[&str] = &["bits", "value"];

#[cfg(not(feature = "serde-str"))]
enum Field {
    Bits,
}
#[cfg(feature = "serde-str")]
enum Field {
    Bits,
    Value,
}

#[cfg(not(feature = "serde-str"))]
impl<'de> Deserialize<'de> for Field {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Field, D::Error> {
        struct FieldVisitor;

        impl<'de> Visitor<'de> for FieldVisitor {
            type Value = Field;

            fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
                formatter.write_str("`bits`")
            }

            fn visit_str<E: de::Error>(self, value: &str) -> Result<Field, E> {
                match value {
                    "bits" => Ok(Field::Bits),
                    _ => Err(de::Error::unknown_field(value, FIELDS)),
                }
            }
        }

        deserializer.deserialize_identifier(FieldVisitor)
    }
}

#[cfg(feature = "serde-str")]
impl<'de> Deserialize<'de> for Field {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Field, D::Error> {
        struct FieldVisitor;

        impl<'de> Visitor<'de> for FieldVisitor {
            type Value = Field;

            fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
                formatter.write_str("`bits` or `value`")
            }

            fn visit_str<E: de::Error>(self, value: &str) -> Result<Field, E> {
                match value {
                    "bits" => Ok(Field::Bits),
                    "value" => Ok(Field::Value),
                    _ => Err(de::Error::unknown_field(value, FIELDS)),
                }
            }
        }

        deserializer.deserialize_identifier(FieldVisitor)
    }
}
