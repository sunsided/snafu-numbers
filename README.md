# Special Numeral-Analogue Fuel Units

A Rust crate and utility to deal with conversions of SNAFU values
from Advent of Code 2022, Day 25 ([here](https://adventofcode.com/2022/day/25)).
The file [AOC-22-25.md](AOC-22-25.md) contains the full puzzle in case the
website is unavailable.

## SNAFU numbers

SNAFU numbers are a base-5 system written right to left, where the first (i.e., right-most)
place represents 5<sup>1</sup> = 5, the second place represents 5<sup>2</sup> = 25,
the third place 5<sup>3</sup> = 625, etc.

These are the digits used, as well as their base-10 integer representation:

| SNAFU digit | Name         | Decimal / ℤ |
|-------------|--------------|-------------|
| `2`         | two          | `2`         |
| `1`         | one          | `1`         |
| `0`         | zero         | `0`         |
| `-`         | minus        | `-1`        |
| `=`         | double-minus | `-2`        |

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
