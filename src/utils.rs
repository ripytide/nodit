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

use crate::discrete_bounds::DiscreteBounds;
use crate::range_bounds_map::DiscreteRange;
use crate::stepable::Discrete;

pub(crate) fn cmp_point_with_range<I, K>(
    point: I,
	range: K,
) -> Ordering
where
    I: Ord,
	K: DiscreteRange<I>,
{
	if point < range.start() {
		Ordering::Less
	} else if point > range.end() {
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
	A: DiscreteRange<I> + Copy,
	B: DiscreteRange<I> + Copy,
	I: Ord,
{
	if a.start() < b.start() {
		match (
			contains_discrete_bound_ord(a, b.start()),
			contains_discrete_bound_ord(a, b.end()),
		) {
			(false, false) => Config::LeftFirstNonOverlapping,
			(true, false) => Config::LeftFirstPartialOverlap,
			(true, true) => Config::LeftContainsRight,
			(false, true) => unreachable!(),
		}
	} else {
		match (
			contains_discrete_bound_ord(b, a.start()),
			contains_discrete_bound_ord(b, a.end()),
		) {
			(false, false) => Config::RightFirstNonOverlapping,
			(true, false) => Config::RightFirstPartialOverlap,
			(true, true) => Config::RightContainsLeft,
			(false, true) => unreachable!(),
		}
	}
}

enum SortedConfig<I> {
	NonOverlapping(
		(DiscreteBoundOrd<I>, DiscreteBoundOrd<I>),
		(DiscreteBoundOrd<I>, DiscreteBoundOrd<I>),
	),
	PartialOverlap(
		(DiscreteBoundOrd<I>, DiscreteBoundOrd<I>),
		(DiscreteBoundOrd<I>, DiscreteBoundOrd<I>),
	),
	Swallowed(
		(DiscreteBoundOrd<I>, DiscreteBoundOrd<I>),
		(DiscreteBoundOrd<I>, DiscreteBoundOrd<I>),
	),
}
fn sorted_config<I, A, B>(a: A, b: B) -> SortedConfig<I>
where
	A: DiscreteRange<I> + Copy,
	B: DiscreteRange<I> + Copy,
	I: Ord,
{
	let ae = (a.start(), a.end());
	let be = (b.start(), b.end());
	match config(a, b) {
		Config::LeftFirstNonOverlapping => SortedConfig::NonOverlapping(ae, be),
		Config::LeftFirstPartialOverlap => SortedConfig::Swallowed(ae, be),
		Config::LeftContainsRight => SortedConfig::Swallowed(ae, be),

		Config::RightFirstNonOverlapping => SortedConfig::NonOverlapping(be, ae),
		Config::RightFirstPartialOverlap => SortedConfig::PartialOverlap(be, ae),
		Config::RightContainsLeft => SortedConfig::Swallowed(be, ae),
	}
}

pub(crate) fn contains_discrete_bound_ord<I, A>(
	range: A,
	discrete_bound_ord: DiscreteBoundOrd<I>,
) -> bool
where
	A: DiscreteRange<I>,
	I: Ord,
{
	cmp_point_with_range(discrete_bound_ord, range).is_eq()
}

#[derive(Debug)]
pub(crate) struct CutResult<I> {
	pub(crate) before_cut: Option<DiscreteBounds<I>>,
	pub(crate) inside_cut: Option<DiscreteBounds<I>>,
	pub(crate) after_cut: Option<DiscreteBounds<I>>,
}
pub(crate) fn cut_range<I, B, C>(base: B, cut: C) -> CutResult<I>
where
	B: DiscreteRange<I> + Copy,
	C: DiscreteRange<I> + Copy,
	I: Ord + Copy + Discrete,
{
	let mut result = CutResult {
		before_cut: None,
		inside_cut: None,
		after_cut: None,
	};

	match config(base, cut) {
		Config::LeftFirstNonOverlapping => {
			result.before_cut = Some(DiscreteBounds {
				start: base.start().into(),
				end: base.end().into(),
			});
		}
		Config::LeftFirstPartialOverlap => {
			result.before_cut = Some(DiscreteBounds {
				start: base.start().into(),
				end: cut.start().down_if_finite().into(),
			});
			result.inside_cut = Some(DiscreteBounds {
				start: cut.start().into(),
				end: base.end().into(),
			});
		}
		Config::LeftContainsRight => {
			result.before_cut = Some(DiscreteBounds {
				start: base.start().into(),
				end: cut.start().down_if_finite().into(),
			});
			result.inside_cut = Some(DiscreteBounds {
				start: cut.start().into(),
				end: cut.end().into(),
			});
			// exception for Unbounded-ending things
			match cut.end() {
				DiscreteBoundOrd::EndUnbounded => {}
				_ => {
					result.after_cut = Some(DiscreteBounds {
						start: cut.end().up_if_finite().into(),
						end: base.end().into(),
					});
				}
			}
		}

		Config::RightFirstNonOverlapping => {
			result.after_cut = Some(DiscreteBounds {
				start: base.start().into(),
				end: base.end().into(),
			});
		}
		Config::RightFirstPartialOverlap => {
			result.after_cut = Some(DiscreteBounds {
				start: cut.end().up_if_finite().into(),
				end: base.end().into(),
			});
			result.inside_cut = Some(DiscreteBounds {
				start: base.start().into(),
				end: cut.end().into(),
			});
		}
		Config::RightContainsLeft => {
			result.inside_cut = Some(DiscreteBounds {
				start: base.start().into(),
				end: base.end().into(),
			});
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
	K: DiscreteRange<I>,
{
	range.start() <= range.end()
}

pub(crate) fn overlaps<I, A, B>(a: A, b: B) -> bool
where
	A: DiscreteRange<I> + Copy,
	B: DiscreteRange<I> + Copy,
	I: Ord,
{
	!matches!(sorted_config(a, b), SortedConfig::NonOverlapping(_, _))
}
