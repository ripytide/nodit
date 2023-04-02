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
use std::ops::{Bound, RangeBounds};

use labels::{tested, trivial};

use crate::bound_ord::BoundOrd;

//todo why is pub(crate) needed?
pub(crate) fn cmp_range_bounds_with_bound_ord<A, B>(
	range_bounds: &A,
	bound_ord: BoundOrd<&B>,
) -> Ordering
where
	A: RangeBounds<B>,
	B: Ord,
{
	if bound_ord < BoundOrd::start(range_bounds.start_bound()) {
		Ordering::Greater
	} else if bound_ord > BoundOrd::end(range_bounds.end_bound()) {
		Ordering::Less
	} else {
		Ordering::Equal
	}
}

#[derive(Debug, PartialEq)]
enum Config {
	LeftFirstNonOverlapping,
	LeftFirstPartialOverlap,
	LeftContainsRight,

	RightFirstNonOverlapping,
	RightFirstPartialOverlap,
	RightContainsLeft,
}

#[tested]
fn config<I, A, B>(a: &A, b: &B) -> Config
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
	I: Ord,
{
	let (a_start, a_end) = expand(a);
	let (b_start, b_end) = expand(b);

	match BoundOrd::start(a_start) < BoundOrd::start(b_start) {
		true => {
			match (
				contains_bound_ord(a, BoundOrd::start(b_start)),
				contains_bound_ord(a, BoundOrd::end(b_end)),
			) {
				(false, false) => Config::LeftFirstNonOverlapping,
				(true, false) => Config::LeftFirstPartialOverlap,
				(true, true) => Config::LeftContainsRight,
				(false, true) => unreachable!(),
			}
		}
		false => {
			match (
				contains_bound_ord(b, BoundOrd::start(a_start)),
				contains_bound_ord(b, BoundOrd::end(a_end)),
			) {
				(false, false) => Config::RightFirstNonOverlapping,
				(true, false) => Config::RightFirstPartialOverlap,
				(true, true) => Config::RightContainsLeft,
				(false, true) => unreachable!(),
			}
		}
	}
}

#[derive(Debug, PartialEq)]
enum SortedConfig<I> {
	NonOverlapping((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
	PartialOverlap((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
	Swallowed((Bound<I>, Bound<I>), (Bound<I>, Bound<I>)),
}

#[rustfmt::skip]//{{{//{{{//{{{//{{{
#[trivial]//}}}//}}}//}}}//}}}
fn sorted_config<'a, I, A, B>(a: &'a A, b: &'a B) -> SortedConfig<&'a I>
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
	I: Ord,
{
    let ae = expand(a);
    let be = expand(b);
	match config(a, b) {
        Config::LeftFirstNonOverlapping => SortedConfig::NonOverlapping(ae, be),
		Config::LeftFirstPartialOverlap => SortedConfig::Swallowed(ae, be),
		Config::LeftContainsRight => SortedConfig::Swallowed(ae, be),

        Config::RightFirstNonOverlapping => SortedConfig::NonOverlapping(be, ae),
        Config::RightFirstPartialOverlap => SortedConfig::PartialOverlap(be, ae),
		Config::RightContainsLeft => SortedConfig::Swallowed(be, ae),
	}
}

#[trivial]
fn contains_bound_ord<I, A>(range_bounds: &A, bound_ord: BoundOrd<&I>) -> bool
where
	A: RangeBounds<I>,
	I: Ord,
{
	let start_bound_ord = BoundOrd::start(range_bounds.start_bound());
	let end_bound_ord = BoundOrd::end(range_bounds.end_bound());

	return bound_ord >= start_bound_ord && bound_ord <= end_bound_ord;
}

#[derive(Debug)]
struct CutResult<I> {
	before_cut: Option<(Bound<I>, Bound<I>)>,
	inside_cut: Option<(Bound<I>, Bound<I>)>,
	after_cut: Option<(Bound<I>, Bound<I>)>,
}

#[tested]
fn cut_range_bounds<'a, I, B, C>(
	base_range_bounds: &'a B,
	cut_range_bounds: &'a C,
) -> CutResult<&'a I>
where
	B: RangeBounds<I>,
	C: RangeBounds<I>,
	I: Ord + Clone,
{
	let base_all @ (base_start, base_end) = (
		base_range_bounds.start_bound(),
		base_range_bounds.end_bound(),
	);
	let cut_all @ (cut_start, cut_end) =
		(cut_range_bounds.start_bound(), cut_range_bounds.end_bound());

	let mut result = CutResult {
		before_cut: None,
		inside_cut: None,
		after_cut: None,
	};

	match config(base_range_bounds, cut_range_bounds) {
		Config::LeftFirstNonOverlapping => {
			result.before_cut = Some(base_all);
		}
		Config::LeftFirstPartialOverlap => {
			result.before_cut = Some((base_start, flip_bound(cut_start)));
			result.inside_cut = Some((cut_start, base_end));
		}
		Config::LeftContainsRight => {
			result.before_cut = Some((base_start, flip_bound(cut_start)));
			result.inside_cut = Some(cut_all);
			// exception for Unbounded-ending things
			match cut_end {
				Bound::Unbounded => {}
				_ => {
					result.after_cut = Some((flip_bound(cut_end), base_end));
				}
			}
		}

		Config::RightFirstNonOverlapping => {
			result.after_cut = Some(base_all);
		}
		Config::RightFirstPartialOverlap => {
			result.after_cut = Some((flip_bound(cut_end), base_end));
			result.inside_cut = Some((base_start, cut_end));
		}
		Config::RightContainsLeft => {
			result.inside_cut = Some(base_all);
		}
	}

	//only return valid range_bounds
	return CutResult {
		before_cut: result
			.before_cut
			.filter(|x| is_valid_range_bounds::<(Bound<&I>, Bound<&I>), I>(x)),
		inside_cut: result
			.inside_cut
			.filter(|x| is_valid_range_bounds::<(Bound<&I>, Bound<&I>), I>(x)),
		after_cut: result
			.after_cut
			.filter(|x| is_valid_range_bounds::<(Bound<&I>, Bound<&I>), I>(x)),
	};
}

#[trivial]
pub fn is_valid_range_bounds<Q, I>(range_bounds: &Q) -> bool
where
	Q: RangeBounds<I>,
	I: std::cmp::PartialOrd,
{
	match (range_bounds.start_bound(), range_bounds.end_bound()) {
		(Bound::Included(start), Bound::Included(end)) => start <= end,
		(Bound::Included(start), Bound::Excluded(end)) => start < end,
		(Bound::Excluded(start), Bound::Included(end)) => start < end,
		(Bound::Excluded(start), Bound::Excluded(end)) => start < end,
		_ => true,
	}
}

#[tested]
fn overlaps<I, A, B>(a: &A, b: &B) -> bool
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
	I: Ord,
{
	!matches!(sorted_config(a, b), SortedConfig::NonOverlapping(_, _))
}

#[tested]
fn touches<I, A, B>(a: &A, b: &B) -> bool
where
	A: RangeBounds<I>,
	B: RangeBounds<I>,
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

#[trivial]
fn expand<I, A>(range_bounds: &A) -> (Bound<&I>, Bound<&I>)
where
	A: RangeBounds<I>,
{
	(range_bounds.start_bound(), range_bounds.end_bound())
}

#[trivial]
fn flip_bound<I>(bound: Bound<&I>) -> Bound<&I> {
	match bound {
		Bound::Included(point) => Bound::Excluded(point),
		Bound::Excluded(point) => Bound::Included(point),
		Bound::Unbounded => Bound::Unbounded,
	}
}
