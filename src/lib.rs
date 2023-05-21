#![doc = include_str!("../README.md")]

use std::error::Error;
use std::fmt::{Display, Formatter};

pub trait TryFromSnafu: Sized {
    /// Converts a string from SNAFU numbers into decimal.
    /// Returns an error if the conversion failed.
    ///
    /// ## Arguments
    /// * `value` - The string value to convert from.
    ///
    /// ## Example
    /// ```
    /// use snafu_numbers::TryFromSnafu;
    /// assert_eq!(u32::try_from_snafu("1=-0-2"), Ok(1747));
    /// ```
    fn try_from_snafu(value: &str) -> Result<Self, ConversionError>;
}

pub trait FromSnafu {
    /// Converts a string from SNAFU numbers into decimal.
    ///
    /// ## Arguments
    /// * `value` - The string value to convert from.
    ///
    /// ## Panics
    /// Panics if the conversion failed. If you need to gracefully fail,
    /// use [`TryFromSnafu`] instead.
    ///
    /// ## Example
    /// ```
    /// use snafu_numbers::FromSnafu;
    /// assert_eq!(u32::from_snafu("1=-0-2"), 1747);
    /// ```
    fn from_snafu(value: &str) -> Self;
}

trait IntoSnafu {
    fn into_snafu(self) -> String;
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ConversionError {
    /// An invalid digit was provided.
    InvalidDigit,
    /// A calculation overflowed.
    Overflow,
    /// The value provided is too large or too small to be
    /// represented by the target type.
    OutOfBounds,
}

impl Display for ConversionError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ConversionError::InvalidDigit => write!(f, "An invalid digit was specified"),
            ConversionError::Overflow => write!(f, "The calculation overflowed"),
            ConversionError::OutOfBounds => {
                write!(f, "The input was out of bounds for the target type")
            }
        }
    }
}

impl Error for ConversionError {}

/// Implements [`TryFromSnafu`] for the given target type.
///
/// ## Macro Arguments
/// * `max_len` - The maximum allowed string length before an overflow occurs.
/// * `target` - The type for which to implement [`TryFromSnafu`].
/// * `lift` - The type to which to lift the calculation in order to allow for negative
///            values in the calculations. Should be a signed type.
macro_rules! impl_try_from {
    ($max_len: literal, $target:ty, $lift:ty) => {
        impl TryFromSnafu for $target {
            fn try_from_snafu(value: &str) -> Result<Self, ConversionError> {
                if value.len() > $max_len {
                    return Err(ConversionError::OutOfBounds);
                }

                let (sum, _) =
                    value
                        .chars()
                        .rev()
                        .try_fold((0 as $lift, 1 as $lift), |(sum, pow), c| {
                            let digit = map_digit(c)?;
                            let value = digit as $lift * pow;
                            Ok((sum + value, pow * 5))
                        })?;

                if sum > (<$target>::MAX as $lift) {
                    return Err(ConversionError::OutOfBounds);
                }

                Ok(sum as $target)
            }
        }
    };
}

impl_try_from!(55, i128, i128);
impl_try_from!(28, i64, i128);
impl_try_from!(28, u64, i128);
impl_try_from!(14, i32, i64);
impl_try_from!(14, u32, i64);
impl_try_from!(7, i16, i32);
impl_try_from!(7, u16, i32);
impl_try_from!(4, i8, i16);
impl_try_from!(4, u8, i16);

impl<T> FromSnafu for T
where
    T: TryFromSnafu,
{
    fn from_snafu(value: &str) -> Self {
        match T::try_from_snafu(value) {
            Ok(value) => value,
            Err(e) => panic!("Unable to convert to SNAFU: {e}"),
        }
    }
}

impl IntoSnafu for u128 {
    fn into_snafu(self) -> String {
        todo!()
    }
}

/// Maps a SNAFU digit to a decimal digit.
fn map_digit(digit: char) -> Result<i8, ConversionError> {
    match digit {
        '2' => Ok(2),
        '1' => Ok(1),
        '0' => Ok(0),
        '-' => Ok(-1),
        '=' => Ok(-2),
        _ => Err(ConversionError::InvalidDigit),
    }
}

/// Calculates the number of bits required to store SNAFU
/// value of the specified length.
#[cfg(test)]
fn num_bits_for_len(len: usize) -> u32 {
    debug_assert_ne!(len, 0, "value must be positive");
    num_bits_for_pos(len - 1)
}

/// Calculates the number of bits required to store SNAFU
/// given the specified highest zero-based digit position.
///
/// ## Value ranges and storage requirements
///
/// | Position | Highest     | num bits (unsigned) | delta (bits) |
/// |----------|-------------|---------------------|--------------|
/// | 0        | `2`         | 2                   | -            |
/// | 1        | `12`        | 4                   | 2            |
/// | 2        | `62`        | 6                   | 2            |
/// | 3        | `312`       | 9                   | 3            |
/// | 4        | `1562`      | 11                  | 2            |
/// | 5        | `7812`      | 13                  | 2            |
/// | 6        | `39062`     | 16                  | 3            |
/// | 7        | `195312`    | 18                  | 2            |
/// | 8        | `976562`    | 20                  | 2            |
/// | 9        | `4882812`   | 23                  | 3            |
/// | 10       | `24414062`  | 25                  | 2            |
/// | 11       | `122070312` | 27                  | 2            |
/// | 12       | `610351562` | 30                  | 3            |
#[cfg(test)]
fn num_bits_for_pos(pos: usize) -> u32 {
    // Beatty sequence for log_2(5)
    // https://oeis.org/A061785
    ((pos + 1) as f32 * 5.0f32.log2()).floor() as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u8_from_snafu_works() {
        assert_eq!(u8::from_snafu("2=0="), 198);
        assert_eq!(u8::from_snafu("21"), 11);
        assert_eq!(u8::from_snafu("2=01"), 201);
        assert_eq!(u8::from_snafu("111"), 31);
        assert_eq!(u8::from_snafu("112"), 32);
        assert_eq!(u8::from_snafu("1-12"), 107);
        assert_eq!(u8::from_snafu("12"), 7);
        assert_eq!(u8::from_snafu("1="), 3);
        assert_eq!(u8::from_snafu("122"), 37);
    }

    #[test]
    fn u16_from_snafu_works() {
        assert_eq!(u16::from_snafu("1=-0-2"), 1747);
        assert_eq!(u16::from_snafu("12111"), 906);
        assert_eq!(u16::from_snafu("2=0="), 198);
        assert_eq!(u16::from_snafu("21"), 11);
        assert_eq!(u16::from_snafu("2=01"), 201);
        assert_eq!(u16::from_snafu("111"), 31);
        assert_eq!(u16::from_snafu("20012"), 1257);
        assert_eq!(u16::from_snafu("112"), 32);
        assert_eq!(u16::from_snafu("1=-1="), 353);
        assert_eq!(u16::from_snafu("1-12"), 107);
        assert_eq!(u16::from_snafu("12"), 7);
        assert_eq!(u16::from_snafu("1="), 3);
        assert_eq!(u16::from_snafu("122"), 37);
    }

    #[test]
    fn u32_from_snafu_works() {
        assert_eq!(u32::from_snafu("1=-0-2"), 1747);
        assert_eq!(u32::from_snafu("12111"), 906);
        assert_eq!(u32::from_snafu("2=0="), 198);
        assert_eq!(u32::from_snafu("21"), 11);
        assert_eq!(u32::from_snafu("2=01"), 201);
        assert_eq!(u32::from_snafu("111"), 31);
        assert_eq!(u32::from_snafu("20012"), 1257);
        assert_eq!(u32::from_snafu("112"), 32);
        assert_eq!(u32::from_snafu("1=-1="), 353);
        assert_eq!(u32::from_snafu("1-12"), 107);
        assert_eq!(u32::from_snafu("12"), 7);
        assert_eq!(u32::from_snafu("1="), 3);
        assert_eq!(u32::from_snafu("122"), 37);
    }

    #[test]
    fn u64_from_snafu_works() {
        assert_eq!(u64::from_snafu("1=-0-2"), 1747);
        assert_eq!(u64::from_snafu("12111"), 906);
        assert_eq!(u64::from_snafu("2=0="), 198);
        assert_eq!(u64::from_snafu("21"), 11);
        assert_eq!(u64::from_snafu("2=01"), 201);
        assert_eq!(u64::from_snafu("111"), 31);
        assert_eq!(u64::from_snafu("20012"), 1257);
        assert_eq!(u64::from_snafu("112"), 32);
        assert_eq!(u64::from_snafu("1=-1="), 353);
        assert_eq!(u64::from_snafu("1-12"), 107);
        assert_eq!(u64::from_snafu("12"), 7);
        assert_eq!(u64::from_snafu("1="), 3);
        assert_eq!(u64::from_snafu("122"), 37);
    }

    #[test]
    fn i128_from_snafu_works() {
        assert_eq!(i128::from_snafu("1=-0-2"), 1747);
        assert_eq!(i128::from_snafu("12111"), 906);
        assert_eq!(i128::from_snafu("2=0="), 198);
        assert_eq!(i128::from_snafu("21"), 11);
        assert_eq!(i128::from_snafu("2=01"), 201);
        assert_eq!(i128::from_snafu("111"), 31);
        assert_eq!(i128::from_snafu("20012"), 1257);
        assert_eq!(i128::from_snafu("112"), 32);
        assert_eq!(i128::from_snafu("1=-1="), 353);
        assert_eq!(i128::from_snafu("1-12"), 107);
        assert_eq!(i128::from_snafu("12"), 7);
        assert_eq!(i128::from_snafu("1="), 3);
        assert_eq!(i128::from_snafu("122"), 37);
    }

    #[test]
    fn highest_number() {
        assert_eq!(naive_num_bits(0), 1); // need 1 bit to store the number 0

        assert_eq!(max_for_length(0), 2); // 2×1
        assert_eq!(naive_num_bits(2), 2);
        assert_eq!(num_bits_for_pos(0), 2);
        assert_eq!(num_bits_for_len(1), 2);

        assert_eq!(max_for_length(1), 12); // 2×1 + 2×5
        assert_eq!(naive_num_bits(12), 4); // +2
        assert_eq!(num_bits_for_pos(1), 4);
        assert_eq!(num_bits_for_len(2), 4);

        assert_eq!(max_for_length(2), 62); // 2×1 + 2×5 + 2×25
        assert_eq!(naive_num_bits(62), 6); // +2
        assert_eq!(num_bits_for_pos(2), 6);

        // boundary of i8 / u8

        assert_eq!(num_bits_for_len(3), 6);
        assert_eq!(naive_num_bits(i8::MAX as u128), 7);
        assert_eq!(naive_num_bits(u8::MAX as u128), 8);

        // i8 / u8 overflow here.

        assert_eq!(max_for_length(3), 312); // 2×1 + 2×5 + 2×25 + 2×125
        assert_eq!(naive_num_bits(312), 9); // +3
        assert_eq!(num_bits_for_pos(3), 9);

        assert_eq!(max_for_length(4), 1562);
        assert_eq!(naive_num_bits(1562), 11); // +2
        assert_eq!(num_bits_for_pos(4), 11);

        assert_eq!(max_for_length(5), 7812);
        assert_eq!(naive_num_bits(7812), 13); // +2
        assert_eq!(num_bits_for_pos(5), 13);

        assert_eq!(max_for_length(6), 39062);
        assert_eq!(naive_num_bits(39062), 16); // +3
        assert_eq!(num_bits_for_pos(6), 16);

        // boundary of i16 / u16

        assert_eq!(num_bits_for_len(7), 16);
        assert_eq!(naive_num_bits(i16::MAX as u128), 15);
        assert_eq!(naive_num_bits(u16::MAX as u128), 16);

        // i16 / u16 overflow here.

        assert_eq!(max_for_length(7), 195312);
        assert_eq!(naive_num_bits(195312), 18); // +2
        assert_eq!(num_bits_for_pos(7), 18);

        assert_eq!(max_for_length(8), 976562);
        assert_eq!(naive_num_bits(976562), 20); // +2
        assert_eq!(num_bits_for_pos(8), 20);

        assert_eq!(max_for_length(9), 4882812);
        assert_eq!(naive_num_bits(4882812), 23); // +3
        assert_eq!(num_bits_for_pos(9), 23);

        assert_eq!(max_for_length(10), 24414062);
        assert_eq!(naive_num_bits(24414062), 25); // +2
        assert_eq!(num_bits_for_pos(10), 25);

        assert_eq!(max_for_length(11), 122070312);
        assert_eq!(naive_num_bits(122070312), 27); // +2
        assert_eq!(num_bits_for_pos(11), 27);

        assert_eq!(max_for_length(12), 610351562);
        assert_eq!(naive_num_bits(610351562), 30); // +3
        assert_eq!(num_bits_for_pos(12), 30);

        assert_eq!(max_for_length(13), 3051757812);
        assert_eq!(naive_num_bits(3051757812), 32); // +2
        assert_eq!(num_bits_for_pos(13), 32);

        // boundary of i32 / u32

        assert_eq!(num_bits_for_len(14), 32);
        assert_eq!(naive_num_bits(i32::MAX as u128), 31);
        assert_eq!(naive_num_bits(u32::MAX as u128), 32);

        // i32 / u32 overflow here.

        assert_eq!(max_for_length(14), 15258789062);
        assert_eq!(naive_num_bits(15258789062), 34); // +2
        assert_eq!(num_bits_for_pos(14), 34);

        assert_eq!(max_for_length(15), 76293945312);
        assert_eq!(naive_num_bits(76293945312), 37); // +3
        assert_eq!(num_bits_for_pos(15), 37);

        assert_eq!(max_for_length(16), 381469726562);
        assert_eq!(naive_num_bits(381469726562), 39); // +2
        assert_eq!(num_bits_for_pos(16), 39);

        assert_eq!(max_for_length(17), 1907348632812);
        assert_eq!(naive_num_bits(1907348632812), 41); // +2
        assert_eq!(num_bits_for_pos(17), 41);

        assert_eq!(max_for_length(18), 9536743164062);
        assert_eq!(naive_num_bits(9536743164062), 44); // +3
        assert_eq!(num_bits_for_pos(18), 44);

        assert_eq!(max_for_length(19), 47683715820312);
        assert_eq!(naive_num_bits(47683715820312), 46); // +2
        assert_eq!(num_bits_for_pos(19), 46);

        assert_eq!(max_for_length(20), 238418579101562);
        assert_eq!(naive_num_bits(238418579101562), 48); // +2
        assert_eq!(num_bits_for_pos(20), 48);

        assert_eq!(max_for_length(21), 1192092895507812);
        assert_eq!(naive_num_bits(1192092895507812), 51); // +3
        assert_eq!(num_bits_for_pos(21), 51);

        assert_eq!(max_for_length(22), 5960464477539062);
        assert_eq!(naive_num_bits(5960464477539062), 53); // +2
        assert_eq!(num_bits_for_pos(22), 53);

        assert_eq!(max_for_length(23), 29802322387695312);
        assert_eq!(naive_num_bits(29802322387695312), 55); // +2
        assert_eq!(num_bits_for_pos(23), 55);

        assert_eq!(max_for_length(24), 149011611938476562);
        assert_eq!(naive_num_bits(149011611938476562), 58); // +3
        assert_eq!(num_bits_for_pos(24), 58);

        assert_eq!(max_for_length(25), 745058059692382812);
        assert_eq!(naive_num_bits(745058059692382812), 60); // +2
        assert_eq!(num_bits_for_pos(25), 60);

        assert_eq!(max_for_length(26), 3725290298461914062);
        assert_eq!(naive_num_bits(3725290298461914062), 62); // +2
        assert_eq!(num_bits_for_pos(26), 62);

        // boundary of i64 / u64

        assert_eq!(num_bits_for_len(27), 62);
        assert_eq!(naive_num_bits(i64::MAX as u128), 63);
        assert_eq!(naive_num_bits(u64::MAX as u128), 64);

        // i64 / u64 overflow here.

        assert_eq!(max_for_length(27), 18626451492309570312);
        assert_eq!(naive_num_bits(18626451492309570312), 65); // +3
        assert_eq!(num_bits_for_pos(27), 65);

        assert_eq!(max_for_length(28), 93132257461547851562);
        assert_eq!(naive_num_bits(93132257461547851562), 67); // +2
        assert_eq!(num_bits_for_pos(28), 67);

        assert_eq!(max_for_length(29), 465661287307739257812);
        assert_eq!(naive_num_bits(465661287307739257812), 69); // +2
        assert_eq!(num_bits_for_pos(29), 69);

        assert_eq!(max_for_length(30), 2328306436538696289062);
        assert_eq!(naive_num_bits(2328306436538696289062), 71); // +2 !! (not +3)
        assert_eq!(num_bits_for_pos(30), 71);

        assert_eq!(max_for_length(31), 11641532182693481445312);
        assert_eq!(naive_num_bits(11641532182693481445312), 74); // +3
        assert_eq!(num_bits_for_pos(31), 74);

        assert_eq!(max_for_length(32), 58207660913467407226562);
        assert_eq!(naive_num_bits(58207660913467407226562), 76); // +2
        assert_eq!(num_bits_for_pos(32), 76);

        assert_eq!(max_for_length(33), 291038304567337036132812);
        assert_eq!(naive_num_bits(291038304567337036132812), 78); // +2
        assert_eq!(num_bits_for_pos(33), 78);

        assert_eq!(max_for_length(34), 1455191522836685180664062);
        assert_eq!(naive_num_bits(1455191522836685180664062), 81); // +3
        assert_eq!(num_bits_for_pos(34), 81);

        assert_eq!(max_for_length(35), 7275957614183425903320312);
        assert_eq!(naive_num_bits(7275957614183425903320312), 83); // +2
        assert_eq!(num_bits_for_pos(35), 83);

        // boundary of i128 / u128

        assert_eq!(max_for_length(54), 138777878078144567552953958511352539062);
        assert_eq!(naive_num_bits(138777878078144567552953958511352539062), 127);
        assert_eq!(num_bits_for_pos(54), 127);

        assert_eq!(num_bits_for_len(55), 127);
        assert_eq!(naive_num_bits(i128::MAX as u128), 127);
        assert_eq!(naive_num_bits(u128::MAX), 128);

        // i128 / u128 overflow here.

        assert_eq!(num_bits_for_pos(55), 130);
    }

    /// Calculates the highest decimal value for a SNAFU number
    /// of the specified length.
    fn max_for_length(len: u32) -> u128 {
        let mut sum: u128 = 0;
        for n in 0..=len {
            sum += 2 * 5_u128.pow(n);
        }
        sum
    }

    /// Gets the number of bits required to store the specified number.
    fn naive_num_bits(value: u128) -> u32 {
        1 + if value == 0 { 0 } else { value.ilog2() }
    }
}
