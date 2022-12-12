# range_bounds_map

[![License](https://img.shields.io/github/license/ripytide/range_bounds_map)](https://www.gnu.org/licenses/agpl-3.0.en.html)
[![Docs](https://img.shields.io/maintenance/yes/2023)](https://docs.rs/range_bounds_set)
[![Maintained](https://img.shields.io/maintenance/yes/2023)](https://github.com/ripytide)
[![Crates.io](https://img.shields.io/crates/v/range_bounds_set)](https://crates.io/crates/range_bounds_set)

<p align="center">
<img src="logo.svg" alt="range_bounds_map_logo" width="350">
</p>

This crate provides [`RangeBoundsMap`] and [`RangeBoundsSet`.]

[`RangeBoundsMap`] is an ordered map of non-overlapping [`RangeBounds`]
based on [`BTreeMap`].

[`RangeBoundsSet`] is an ordered set of non-overlapping [`RangeBounds`]
based on [`RangeBoundsMap`].

## Example using [`Range`]s

```rust
use range_bounds_map::RangeBoundsMap;

let mut range_bounds_map = RangeBoundsMap::new();

range_bounds_map.insert_platonic(0..5, true);
range_bounds_map.insert_platonic(5..10, false);

assert_eq!(range_bounds_map.overlaps(&(-2..12)), true);
assert_eq!(range_bounds_map.contains_point(&20), false);
assert_eq!(range_bounds_map.contains_point(&5), true);
```

## Example using a custom [`RangeBounds`] type

```rust
use std::ops::{Bound, RangeBounds};

use range_bounds_map::RangeBoundsMap;

#[derive(Debug)]
enum Reservation {
	// Start, End (Inclusive-Inclusive)
	Finite(u8, u8),
	// Start (Exclusive)
	Infinite(u8),
}

// First, we need to implement RangeBounds
impl RangeBounds<u8> for Reservation {
	fn start_bound(&self) -> Bound<&u8> {
		match self {
			Reservation::Finite(start, _) => {
				Bound::Included(start)
			}
			Reservation::Infinite(start) => {
				Bound::Excluded(start)
			}
		}
	}
	fn end_bound(&self) -> Bound<&u8> {
		match self {
			Reservation::Finite(_, end) => Bound::Included(end),
			Reservation::Infinite(_) => Bound::Unbounded,
		}
	}
}

// Next we can create a custom typed RangeBoundsMap
let reservation_map = RangeBoundsMap::try_from([
	(Reservation::Finite(10, 20), "Ferris".to_string()),
	(Reservation::Infinite(20), "Corro".to_string()),
])
.unwrap();

for (reservation, name) in reservation_map.overlapping(&(16..17))
{
	println!(
		"{name} has reserved {reservation:?} inside the range 16..17"
	);
}

for (reservation, name) in reservation_map.iter() {
	println!("{name} has reserved {reservation:?}");
}

assert_eq!(
	reservation_map.overlaps(&Reservation::Infinite(0)),
	true
);
```

## Key Definitions:

### Overlap

Two `RangeBounds` are "overlapping" if there exists a point that is
contained within both `RangeBounds`.

### Touching

Two `RangeBounds` are "touching" if they do not overlap and
there exists no value between them. For example, `2..4` and
`4..6` are touching but `2..4` and `6..8` are not, neither are
`2..6` and `4..8`.

### Coalesce

When a `RangeBounds` "coalesces" other `RangeBounds` it absorbs them
to become larger.

# Improvements/Caveats

- Missing some functions common to BTreeMap and BTreeSet like:
  - `clear()`
  - `is_subset()`
  - etc... prob a bunch more
- Not particularly optimized, (which doesn't mean it's neccessarily slow)
- Can't use TryFrom<(Bound, Bound)> instead of [`TryFromBounds`] (relys on
  upstream to impl, see [this thread](https://internals.rust-lang.org/t/range-should-impl-tryfrom-bound-bound))

# Credit

I originally came up with the `StartBound`: [`Ord`] bodge on my own,
however, I later stumbled across [`rangemap`] which also used a
`StartBound`: [`Ord`] bodge. [`rangemap`] then became my main source
of inspiration.

The aim for my library was to become a more generic
superset of [`rangemap`], following from [this
issue](https://github.com/jeffparsons/rangemap/issues/56) and [this
pull request](https://github.com/jeffparsons/rangemap/pull/57) in
which I changed [`rangemap`]'s [`RangeMap`] to use [`RangeBounds`]s as
keys before I realized it might be easier and simpler to just write it
all from scratch. Which ended up working really well with some
simplifications (BoundOrd) I made which made some of the code much
easier to work with.

# Similar Crates

Here are some relevant crates I found whilst searching around the
topic area:

- <https://docs.rs/rangemap>
  Very similar to this crate but can only use [`Range`]s and
  [`RangeInclusive`]s as keys in it's `map` and `set` structs (separately).
- <https://docs.rs/ranges>
  Cool library for fully-generic ranges (unlike std::ops ranges), along
  with a `Ranges` datastructure for storing them (Vec-based
  unfortunately)
- <https://docs.rs/intervaltree>
  Allows overlapping intervals but is immutable unfortunately
- <https://docs.rs/nonoverlapping_interval_tree>
  Very similar to rangemap except without a `gaps()` function and only
  for [`Range`]s and not [`RangeInclusive`]s. And also no fancy coalescing
  functions.
- <https://docs.rs/unbounded-interval-tree>
  A data structure based off of a 2007 published paper! It supports any
  RangeBounds as keys too, except it is implemented with a non-balancing
  `Box<Node>` based tree, however it also supports overlapping
  RangeBounds which my library does not.
- <https://docs.rs/rangetree>
  I'm not entirely sure what this library is or isn't, but it looks like
  a custom red-black tree/BTree implementation used specifically for a
  Range Tree. Interesting but also quite old (5 years) and uses
  unsafe.

[`btreemap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
[`btreeset`]: https://doc.rust-lang.org/std/collections/struct.BTreeSet.html
[`rangebounds`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html
[`start_bound()`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html#tymethod.start_bound
[`end_bound()`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html#tymethod.end_bound
[`range`]: https://doc.rust-lang.org/std/ops/struct.Range.html
[`range()`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html#method.range
[`rangemap`]: https://docs.rs/rangemap/latest/rangemap/
[`rangeinclusivemap`]: https://docs.rs/rangemap/latest/rangemap/inclusive_map/struct.RangeInclusiveMap.html#
[`rangeinclusive`]: https://doc.rust-lang.org/std/ops/struct.RangeInclusive.html
[`ord`]: https://doc.rust-lang.org/std/cmp/trait.Ord.html
[`RangeBoundsMap`]: https://docs.rs/range_bounds_map/latest/range_bounds_map/range_bounds_map/struct.RangeBoundsMap.html
[`RangeBoundsSet`]: https://docs.rs/range_bounds_map/latest/range_bounds_map/range_bounds_set/struct.RangeBoundsSet.html
