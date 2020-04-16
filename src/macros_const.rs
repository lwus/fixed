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

// split shift in two parts in case it is equal to 128
macro_rules! split {
    ($CONST:ident >> (128 - $frac:expr)) => {
        consts::$CONST >> (64 - $frac / 2) >> (64 + $frac / 2 - $frac)
    };
}

macro_rules! fixed_const {
    (
        $Fixed:ident[$s_fixed:expr](
            $LeEqU:tt, $LeEqU_C0:tt, $LeEqU_C1:tt, $LeEqU_C2:tt, $LeEqU_C3:tt
        )
    ) => {
        // 0 ≤ constant < 0.5
        impl<Frac: $LeEqU> $Fixed<Frac> {
            /// 1/τ = 0.159154…
            pub const FRAC_1_TAU: U0F128 = split!(consts::FRAC_1_TAU >> (128 - Frac::U32));

            /// 2/τ = 0.318309…
            pub const FRAC_2_TAU: U0F128 = split!(consts::FRAC_2_TAU >> (128 - Frac::U32));

            /// π/8 = 0.392699…
            pub const FRAC_PI_8: U0F128 = split!(consts::FRAC_PI_8 >> (128 - Frac::U32));

            /// 1/π = 0.318309…
            pub const FRAC_1_PI: U0F128 = split!(consts::FRAC_1_PI >> (128 - Frac::U32));

            /// log<sub>10</sub> 2 = 0.301029…
            pub const LOG10_2: U0F128 = split!(consts::LOG10_2 >> (128 - Frac::U32));

            /// log<sub>10</sub> e = 0.434294…
            pub const LOG10_E: U0F128 = split!(consts::LOG10_E >> (128 - Frac::U32));
        }

        // 0.5 ≤ constant < 1
        impl<Frac: $LeEqU_C0> $Fixed<Frac> {
            /// τ/8 = 0.785398…
            pub const FRAC_TAU_8: U0F128 = split!(consts::FRAC_TAU_8 >> (128 - Frac::U32));

            /// τ/12 = 0.523598…
            pub const FRAC_TAU_12: U0F128 = split!(consts::FRAC_TAU_12 >> (128 - Frac::U32));

            /// 4/τ = 0.636619…
            pub const FRAC_4_TAU: U0F128 = split!(consts::FRAC_4_TAU >> (128 - Frac::U32));

            /// π/4 = 0.785398…
            pub const FRAC_PI_4: U0F128 = split!(consts::FRAC_PI_4 >> (128 - Frac::U32));

            /// π/6 = 0.523598…
            pub const FRAC_PI_6: U0F128 = split!(consts::FRAC_PI_6 >> (128 - Frac::U32));

            /// 2/π = 0.636619…
            pub const FRAC_2_PI: U0F128 = split!(consts::FRAC_2_PI >> (128 - Frac::U32));

            /// 1/√2 = 0.707106…
            pub const FRAC_1_SQRT_2: U0F128 = split!(consts::FRAC_1_SQRT_2 >> (128 - Frac::U32));

            /// ln 2 = 0.693147…
            pub const LN_2: U0F128 = split!(consts::LN_2 >> (128 - Frac::U32));
        }

        // 1 ≤ constant < 2
        impl<Frac: $LeEqU_C1> $Fixed<Frac> {
            /// τ/4 = 1.57079…
            pub const FRAC_TAU_4: U1F127 = consts::FRAC_TAU_4 >> (127 - Frac::U32);

            /// τ/6 = 1.04719…
            pub const FRAC_TAU_6: U1F127 = consts::FRAC_TAU_6 >> (127 - Frac::U32);

            /// π/2 = 1.57079…
            pub const FRAC_PI_2: U1F127 = consts::FRAC_PI_2 >> (127 - Frac::U32);

            /// π/3 = 1.04719…
            pub const FRAC_PI_3: U1F127 = consts::FRAC_PI_3 >> (127 - Frac::U32);

            /// 2/√π = 1.12837…
            pub const FRAC_2_SQRT_PI: U1F127 = consts::FRAC_2_SQRT_PI >> (127 - Frac::U32);

            /// √2 = 1.41421…
            pub const SQRT_2: U1F127 = consts::SQRT_2 >> (127 - Frac::U32);

            /// log<sub>2</sub> e = 1.44269…
            pub const LOG2_E: U1F127 = consts::LOG2_E >> (127 - Frac::U32);
        }

        // 2 ≤ constant < 4
        impl<Frac: $LeEqU_C2> $Fixed<Frac> {
            /// τ/2 = 3.14159…
            pub const FRAC_TAU_2: U2F126 = consts::FRAC_TAU_2 >> (126 - Frac::U32);

            /// τ/3 = 2.09439…
            pub const FRAC_TAU_3: U2F126 = consts::FRAC_TAU_3 >> (126 - Frac::U32);

            /// π = 3.14159…
            pub const PI: U2F126 = consts::PI >> (126 - Frac::U32);

            /// e = 2.71828…
            pub const E: U2F126 = consts::E >> (126 - Frac::U32);

            /// log<sub>2</sub> 10 = 3.32192…
            pub const LOG2_10: U2F126 = consts::LOG2_10 >> (126 - Frac::U32);

            /// ln 10 = 2.30258…
            pub const LN_10: U2F126 = consts::LN_10 >> (126 - Frac::U32);
        }

        // 4 ≤ constant < 8
        impl<Frac: $LeEqU_C3> $Fixed<Frac> {
            /// τ = 6.28318…
            pub const TAU: U3F125 = consts::TAU >> (125 - Frac::U32);
        }
    };
}
