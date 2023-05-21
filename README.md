# Special Numeral-Analogue Fuel Units

A Rust crate and utility to deal with conversions of SNAFU values
from Advent of Code 2022, Day 25 ([here](https://adventofcode.com/2022/day/25)).
The file [AOC-22-25.md](AOC-22-25.md) contains the full puzzle in case the
website is unavailable.

## SNAFU numbers

SNAFU numbers are a power-of-5 centric base-10 system written right to left.
The zero-th (i.e., right-most) place represents a multiple of 5<sup>0</sup> = 0, the first 
represents a multiple 5<sup>1</sup> = 5, the second place 5<sup>2</sup> = 25,
the third place 5<sup>3</sup> = 625, etc.

Five different digits are used. Here is a list alongside their decimal integer representation:

| SNAFU digit | Name         | Decimal / ℤ |
|-------------|--------------|-------------|
| `2`         | two          | `2`         |
| `1`         | one          | `1`         |
| `0`         | zero         | `0`         |
| `-`         | minus        | `-1`        |
| `=`         | double-minus | `-2`        |

As a result, the individual values in each position `n` is 2×5<sup>n-1</sup>, so

| Position | Base                   | `=`     | `-`     | `0` | `1`    | `2`    |
|----------|------------------------|---------|---------|-----|--------|--------|
| 0        | 5<sup>0</sup> = `1`    | `-2`    | `1`     | `0` | `1`    | `2`    |
| 1        | 5<sup>1</sup> = `5`    | `-10`   | `-5`    | `0` | `5`    | `10`   |
| 2        | 5<sup>2</sup> = `25`   | `-50`   | `-25`   | `0` | `25`   | `50`   |
| 3        | 5<sup>3</sup> = `125`  | `-250`  | `-125`  | `0` | `125`  | `250`  |
| 4        | 5<sup>4</sup> = `625`  | `-1250` | `-625`  | `0` | `625`  | `1250` |
| 5        | 5<sup>5</sup> = `3125` | `-6250` | `-3125` | `0` | `3125` | `6250` |

etc.

To quote the rules:

> Say you have the SNAFU number `2=-01`. That's `2` in
the 625s place, `=` (double-minus) in the 125s place, `-` (minus) in the 25s place,
`0` in the 5s place, and 1 in the `1`s place.
(2 times 625) plus (-2 times 125) plus (-1 times 25) plus (0 times 5) plus (1 times 1).
That's 1250 plus -250 plus -25 plus 0 plus 1. **976**!"

### Example conversion from decimal to SNAFU

| Decimal     | SNAFU           |
|-------------|-----------------|
| `1`         | `1`             |
| `2`         | `2`             |
| `3`         | `1=`            |
| `4`         | `1-`            |
| `5`         | `10`            |
| `6`         | `11`            |
| `7`         | `12`            |
| `8`         | `2=`            |
| `9`         | `2-`            |
| `10`        | `20`            |
| `15`        | `1=0`           |
| `20`        | `1-0`           |
| `2022`      | `1=11-2`        |
| `12345`     | `1-0---0`       |
| `314159265` | `1121-1110-1=0` |

### Example conversion from SNAFU to decimal

| SNAFU    | Decimal |
|----------|---------|
| `1=-0-2` | `1747`  |
| `12111`  | `906`   |
| `2=0=`   | `198`   |
| `21`     | `11`    |
| `2=01`   | `201`   |
| `111`    | `31`    |
| `20012`  | `1257`  |
| `112`    | `32`    |
| `1=-1=`  | `353`   |
| `1-12`   | `107`   |
| `12`     | `7`     |
| `1=`     | `3`     |
| `122`    | `37`    |
