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

use std::cmp::Ordering;
use std::ops::Bound;

use crate::bound_ord::BoundOrd;
use crate::range_bounds_map::NiceRange;
use crate::{TryFromBounds, TryFromBoundsError};

pub(crate) fn cmp_range_with_bound_ord<A, B>(
	range: A,
	bound_ord: BoundOrd<B>,
) -> Ordering
where
	A: NiceRange<B>,
	B: Ord,
{
	if bound_ord < BoundOrd::start(range.start()) {
		Ordering::Less
	} else if bound_ord > BoundOrd::end(range.end()) {
		Ordering::Greater
	} else {
		Ordering::Equal
	}
}

#[derive(Debug, PartialEq)]
pub(crate) enum Config {
	LeftFirstNonOverlapping,
	LeftFirstPartialOverlap,
	LeftContainsRight,

	RightFirstNonOverlapping,
	RightFirstPartialOverlap,
	RightContainsLeft,
}
pub(crate) fn config<I, A, B>(a: A, b: B) -> Config
where
	A: NiceRange<I>,
	B: NiceRange<I>,
	I: Ord,
{
	match BoundOrd::start(a.start()) < BoundOrd::start(b.start()) {
		true => {
			match (
				contains_bound_ord(a, BoundOrd::start(b.start())),
				contains_bound_ord(a, BoundOrd::end(b.end())),
			) {
				(false, false) => Config::LeftFirstNonOverlapping,
				(true, false) => Config::LeftFirstPartialOverlap,
				(true, true) => Config::LeftContainsRight,
				(false, true) => unreachable!(),
			}
		}
		false => {
			match (
				contains_bound_ord(b, BoundOrd::start(a.start())),
				contains_bound_ord(b, BoundOrd::end(a.end())),
			) {
				(false, false) => Config::RightFirstNonOverlapping,
				(true, false) => Config::RightFirstPartialOverlap,
				(true, true) => Config::RightContainsLeft,
				(false, true) => unreachable!(),
			}
		}
	}
}

enum SortedConfig<I> {
	NonOverlapping((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
	PartialOverlap((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
	Swallowed((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
}
fn sorted_config<I, A, B>(a: A, b: B) -> SortedConfig<I>
where
	A: NiceRange<I>,
	B: NiceRange<I>,
	I: Ord,
{
	let ae = (a.start(), a.end());
	let be = (b.start(), b.end());
	match config(a, b) {
		Config::LeftFirstNonOverlapping => SortedConfig::NonOverlapping(ae, be),
		Config::LeftFirstPartialOverlap => SortedConfig::Swallowed(ae, be),
		Config::LeftContainsRight => SortedConfig::Swallowed(ae, be),

		Config::RightFirstNonOverlapping => {
			SortedConfig::NonOverlapping(be, ae)
		}
		Config::RightFirstPartialOverlap => {
			SortedConfig::PartialOverlap(be, ae)
		}
		Config::RightContainsLeft => SortedConfig::Swallowed(be, ae),
	}
}

pub(crate) fn contains_bound_ord<I, A>(range: A, bound_ord: BoundOrd<I>) -> bool
where
	A: NiceRange<I>,
	I: Ord,
{
	let start_bound_ord = BoundOrd::start(range.start());
	let end_bound_ord = BoundOrd::end(range.end());

	return bound_ord >= start_bound_ord && bound_ord <= end_bound_ord;
}

#[derive(Debug)]
pub(crate) struct CutResult<I> {
	pub(crate) before_cut: Option<(Bound<I>, Bound<I>)>,
	pub(crate) inside_cut: Option<(Bound<I>, Bound<I>)>,
	pub(crate) after_cut: Option<(Bound<I>, Bound<I>)>,
}
pub(crate) fn cut_range<I, B, C>(base: B, cut: C) -> CutResult<I>
where
	B: NiceRange<I>,
	C: NiceRange<I>,
	I: Ord + Copy,
{
	let mut result = CutResult {
		before_cut: None,
		inside_cut: None,
		after_cut: None,
	};

	match config(base, cut) {
		Config::LeftFirstNonOverlapping => {
			result.before_cut = Some((base.start(), base.end()));
		}
		Config::LeftFirstPartialOverlap => {
			result.before_cut = Some((base.start(), flip_bound(cut.start())));
			result.inside_cut = Some((cut.start(), base.end()));
		}
		Config::LeftContainsRight => {
			result.before_cut = Some((base.start(), flip_bound(cut.start())));
			result.inside_cut = Some((cut.start(), cut.end()));
			// exception for Unbounded-ending things
			match cut.end() {
				Bound::Unbounded => {}
				_ => {
					result.after_cut =
						Some((flip_bound(cut.end()), base.end()));
				}
			}
		}

		Config::RightFirstNonOverlapping => {
			result.after_cut = Some((base.start(), base.end()));
		}
		Config::RightFirstPartialOverlap => {
			result.after_cut = Some((flip_bound(cut.end()), base.end()));
			result.inside_cut = Some((base.start(), cut.end()));
		}
		Config::RightContainsLeft => {
			result.inside_cut = Some((base.start(), base.end()));
		}
	}

	//only return valid range_bounds
	return CutResult {
		before_cut: result.before_cut.filter(|x| is_valid_range(*x)),
		inside_cut: result.inside_cut.filter(|x| is_valid_range(*x)),
		after_cut: result.after_cut.filter(|x| is_valid_range(*x)),
	};
}

pub(crate) fn is_valid_range<I, K>(range: K) -> bool
where
	I: Ord,
	K: NiceRange<I>,
{
	match (range.start(), range.end()) {
		(Bound::Included(start), Bound::Included(end)) => start <= end,
		(Bound::Included(start), Bound::Excluded(end)) => start < end,
		(Bound::Excluded(start), Bound::Included(end)) => start < end,
		(Bound::Excluded(start), Bound::Excluded(end)) => start < end,
		_ => true,
	}
}

pub(crate) fn overlaps<I, A, B>(a: A, b: B) -> bool
where
	A: NiceRange<I>,
	B: NiceRange<I>,
	I: Ord,
{
	!matches!(sorted_config(a, b), SortedConfig::NonOverlapping(_, _))
}

pub(crate) fn touches<I, A, B>(a: A, b: B) -> bool
where
	A: NiceRange<I>,
	B: NiceRange<I>,
	I: Ord,
{
	match sorted_config(a, b) {
		SortedConfig::NonOverlapping(a, b) => match (a.1, b.0) {
			(Bound::Included(point1), Bound::Excluded(point2)) => {
				point1 == point2
			}
			(Bound::Excluded(point1), Bound::Included(point2)) => {
				point1 == point2
			}
			_ => false,
		},
		_ => false,
	}
}

pub(crate) fn flip_bound<I>(bound: Bound<I>) -> Bound<I> {
	match bound {
		Bound::Included(point) => Bound::Excluded(point),
		Bound::Excluded(point) => Bound::Included(point),
		Bound::Unbounded => Bound::Unbounded,
	}
}
