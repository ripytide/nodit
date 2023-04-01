/*
Copyright 2022 James Forster

This file is part of range_bounds_map.

range_bounds_map is free software: you can redistribute it and/or
modify it under the terms of the GNU Affero General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

range_bounds_map is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with range_bounds_map. If not, see <https://www.gnu.org/licenses/>.
*/

//! This crate provides [`RangeBoundsMap`] and [`RangeBoundsSet`].
//!
//! [`RangeBoundsMap`] is an ordered map of non-overlapping [`RangeBounds`]
//! based on [`BTreeMap`].
//!
//! [`RangeBoundsSet`] is an ordered set of non-overlapping [`RangeBounds`]
//! based on [`RangeBoundsMap`].
//!
//! ## Example using [`Range`]s
//!
//! ```rust
//! use range_bounds_map::RangeBoundsMap;
//!
//! let mut map = RangeBoundsMap::new();
//!
//! map.insert_strict(0..5, true);
//! map.insert_strict(5..10, false);
//!
//! assert_eq!(map.overlaps(&(-2..12)), true);
//! assert_eq!(map.contains_point(&20), false);
//! assert_eq!(map.contains_point(&5), true);
//! ```
//!
//! ## Example using a custom [`RangeBounds`] type
//!
//! ```rust
//! use std::ops::{Bound, RangeBounds};
//!
//! use range_bounds_map::RangeBoundsMap;
//!
//! #[derive(Debug)]
//! enum Reservation {
//! 	// Start, End (Inclusive-Inclusive)
//! 	Finite(u8, u8),
//! 	// Start (Exclusive)
//! 	Infinite(u8),
//! }
//!
//! // First, we need to implement RangeBounds
//! impl RangeBounds<u8> for Reservation {
//! 	fn start_bound(&self) -> Bound<&u8> {
//! 		match self {
//! 			Reservation::Finite(start, _) => {
//! 				Bound::Included(start)
//! 			}
//! 			Reservation::Infinite(start) => {
//! 				Bound::Excluded(start)
//! 			}
//! 		}
//! 	}
//! 	fn end_bound(&self) -> Bound<&u8> {
//! 		match self {
//! 			Reservation::Finite(_, end) => Bound::Included(end),
//! 			Reservation::Infinite(_) => Bound::Unbounded,
//! 		}
//! 	}
//! }
//!
//! // Next we can create a custom typed RangeBoundsMap
//! let reservation_map = RangeBoundsMap::from_slice_strict([
//! 	(Reservation::Finite(10, 20), "Ferris".to_string()),
//! 	(Reservation::Infinite(20), "Corro".to_string()),
//! ])
//! .unwrap();
//!
//! for (reservation, name) in reservation_map.overlapping(&(16..17))
//! {
//! 	println!(
//! 		"{name} has reserved {reservation:?} inside the range 16..17"
//! 	);
//! }
//!
//! for (reservation, name) in reservation_map.iter() {
//! 	println!("{name} has reserved {reservation:?}");
//! }
//!
//! assert_eq!(
//! 	reservation_map.overlaps(&Reservation::Infinite(0)),
//! 	true
//! );
//! ```
//!
//! ## Key Definitions:
//!
//! ### Invalid RangeBounds
//!
//! Within this crate, not all `RangeBounds` are considered valid
//! `RangeBounds`. The definition of the validity of a `RangeBounds` used
//! within this crate is that a `RangeBounds` is only valid if it contains
//! at least one value of the underlying domain.
//!
//! For example, `4..6` is considered valid as it contains the values `4`
//! and `5`, however, `4..4` is considered invalid as it contains no
//! values. Another example of invalid `RangeBounds` are those with
//! `start_bound()`s with greater values than their `end_bound()`s, such
//! as `5..2` or `100..=40`.
//!
//! Here are a few examples of `RangeBounds` and whether they are valid:
//!
//! | `RangeBounds`  | Valid |
//! | -------------- | ----- |
//! | 0..0           | NO    |
//! | 0..1           | YES   |
//! | 9..8           | NO    |
//! | (0.4)..=(-0.2) | NO    |
//! | ..(-3)         | YES   |
//! | 0.0003..       | YES   |
//! | ..             | YES   |
//! | 400..=400      | YES   |
//!
//! ### Overlap
//!
//! Two `RangeBounds` are "overlapping" if there exists a point that is
//! contained within both `RangeBounds`.
//!
//! ### Touching
//!
//! Two `RangeBounds` are "touching" if they do not overlap and
//! there exists no value between them. For example, `2..4` and
//! `4..6` are touching but `2..4` and `6..8` are not, neither are
//! `2..6` and `4..8`.
//!
//! ### Merging
//!
//! When a `RangeBounds` "merges" other `RangeBounds` it absorbs them
//! to become larger.
//!
//! ### Further Reading
//!
//! See Wikipedia's article on Intervals:
//! <https://en.wikipedia.org/wiki/Interval_(mathematics)>
//!
//! # Improvements/Caveats
//!
//! - Missing some functions common to BTreeMap and BTreeSet like:
//!   - `clear()`
//!   - `is_subset()`
//!   - etc... prob a bunch more
//! - Not particularly optimized, (which doesn't mean it's neccessarily slow)
//! - Can't use TryFrom<(Bound, Bound)> instead of [`TryFromBounds`] (relys on
//!   upstream to impl, see [this thread](https://internals.rust-lang.org/t/range-should-impl-tryfrom-bound-bound))
//!
//! # Credit
//!
//! I originally came up with the `StartBound`: [`Ord`] bodge on my own,
//! however, I later stumbled across [`rangemap`] which also used a
//! `StartBound`: [`Ord`] bodge. [`rangemap`] then became my main source
//! of inspiration.
//!
//! The aim for my library was to become a more generic
//! superset of [`rangemap`], following from [this
//! issue](https://github.com/jeffparsons/rangemap/issues/56) and [this
//! pull request](https://github.com/jeffparsons/rangemap/pull/57) in
//! which I changed [`rangemap`]'s [`RangeMap`] to use [`RangeBounds`]s as
//! keys before I realized it might be easier and simpler to just write it
//! all from scratch. Which ended up working really well with some
//! simplifications (BoundOrd) I made which made some of the code much
//! easier to work with.
//!
//! # Similar Crates
//!
//! Here are some relevant crates I found whilst searching around the
//! topic area:
//!
//! - <https://docs.rs/rangemap>
//!   Very similar to this crate but can only use [`Range`]s and
//!   [`RangeInclusive`]s as keys in it's `map` and `set` structs (separately).
//! - <https://docs.rs/btree-range-map>
//! - <https://docs.rs/ranges>
//!   Cool library for fully-generic ranges (unlike std::ops ranges), along
//!   with a `Ranges` datastructure for storing them (Vec-based
//!   unfortunately)
//! - <https://docs.rs/intervaltree>
//!   Allows overlapping intervals but is immutable unfortunately
//! - <https://docs.rs/nonoverlapping_interval_tree>
//!   Very similar to rangemap except without a `gaps()` function and only
//!   for [`Range`]s and not [`RangeInclusive`]s. And also no fancy coalescing
//!   functions.
//! - <https://docs.rs/unbounded-interval-tree>
//!   A data structure based off of a 2007 published paper! It supports any
//!   RangeBounds as keys too, except it is implemented with a non-balancing
//!   `Box<Node>` based tree, however it also supports overlapping
//!   RangeBounds which my library does not.
//! - <https://docs.rs/rangetree>
//!   I'm not entirely sure what this library is or isn't, but it looks like
//!   a custom red-black tree/BTree implementation used specifically for a
//!   Range Tree. Interesting but also quite old (5 years) and uses
//!   unsafe.
//!
//! [`btreemap`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
//! [`btreeset`]: https://doc.rust-lang.org/std/collections/struct.BTreeSet.html
//! [`rangebounds`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html
//! [`start_bound()`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html#tymethod.start_bound
//! [`end_bound()`]: https://doc.rust-lang.org/std/ops/trait.RangeBounds.html#tymethod.end_bound
//! [`range`]: https://doc.rust-lang.org/std/ops/struct.Range.html
//! [`range()`]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html#method.range
//! [`rangemap`]: https://docs.rs/rangemap/latest/rangemap/
//! [`rangeinclusivemap`]: https://docs.rs/rangemap/latest/rangemap/inclusive_map/struct.RangeInclusiveMap.html#
//! [`rangeinclusive`]: https://doc.rust-lang.org/std/ops/struct.RangeInclusive.html
//! [`ord`]: https://doc.rust-lang.org/std/cmp/trait.Ord.html
//! [`RangeBoundsMap`]: https://docs.rs/range_bounds_map/latest/range_bounds_map/range_bounds_map/struct.RangeBoundsMap.html
//! [`RangeBoundsSet`]: https://docs.rs/range_bounds_map/latest/range_bounds_map/range_bounds_set/struct.RangeBoundsSet.html

#![feature(is_some_and)]
#![feature(let_chains)]
#![feature(btree_cursors)]
#![allow(clippy::tabs_in_doc_comments)]
#![allow(clippy::needless_return)]
pub(crate) mod bound_ord;
pub mod range_bounds_map;
pub mod range_bounds_set;
pub mod try_from_bounds;

pub use crate::range_bounds_map::{
	OverlapError, OverlapOrTryFromBoundsError, RangeBoundsMap,
	TryFromBoundsError,
};
pub use crate::range_bounds_set::RangeBoundsSet;
pub use crate::try_from_bounds::TryFromBounds;
