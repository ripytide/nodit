/*
Copyright 2022 James Forster

This file is part of discrete_range_map.

discrete_range_map is free software: you can redistribute it and/or
modify it under the terms of the GNU Affero General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

discrete_range_map is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with discrete_range_map. If not, see <https://www.gnu.org/licenses/>.
*/

use std::cmp::Ordering;

use crate::discrete_finite::DiscreteFinite;
use crate::discrete_range_map::FiniteRange;
use crate::interval::Interval;

pub(crate) fn cmp_point_with_range<I, K>(point: I, range: K) -> Ordering
where
	I: Ord,
	K: FiniteRange<I>,
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
	A: FiniteRange<I> + Copy,
	B: FiniteRange<I> + Copy,
	I: Ord,
{
	if a.start() < b.start() {
		match (contains_point(a, b.start()), contains_point(a, b.end())) {
			(false, false) => Config::LeftFirstNonOverlapping,
			(true, false) => Config::LeftFirstPartialOverlap,
			(true, true) => Config::LeftContainsRight,
			(false, true) => unreachable!(),
		}
	} else {
		match (contains_point(b, a.start()), contains_point(b, a.end())) {
			(false, false) => Config::RightFirstNonOverlapping,
			(true, false) => Config::RightFirstPartialOverlap,
			(true, true) => Config::RightContainsLeft,
			(false, true) => unreachable!(),
		}
	}
}

enum SortedConfig<I> {
	NonOverlapping(Interval<I>, Interval<I>),
	PartialOverlap(Interval<I>, Interval<I>),
	Swallowed(Interval<I>, Interval<I>),
}
fn sorted_config<I, A, B>(a: A, b: B) -> SortedConfig<I>
where
	A: FiniteRange<I> + Copy,
	B: FiniteRange<I> + Copy,
	I: Ord,
{
	let ae = Interval {
		start: a.start(),
		end: a.end(),
	};
	let be = Interval {
		start: b.start(),
		end: b.end(),
	};
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

pub(crate) fn contains_point<I, A>(range: A, point: I) -> bool
where
	A: FiniteRange<I>,
	I: Ord,
{
	cmp_point_with_range(point, range).is_eq()
}

#[derive(Debug)]
pub(crate) struct CutResult<I> {
	pub(crate) before_cut: Option<Interval<I>>,
	pub(crate) inside_cut: Option<Interval<I>>,
	pub(crate) after_cut: Option<Interval<I>>,
}
pub(crate) fn cut_range<I, B, C>(base: B, cut: C) -> CutResult<I>
where
	B: FiniteRange<I> + Copy,
	C: FiniteRange<I> + Copy,
	I: Ord + Copy + DiscreteFinite,
{
	let mut result = CutResult {
		before_cut: None,
		inside_cut: None,
		after_cut: None,
	};

	match config(base, cut) {
		Config::LeftFirstNonOverlapping => {
			result.before_cut = Some(Interval {
				start: base.start(),
				end: base.end(),
			});
		}
		Config::LeftFirstPartialOverlap => {
			result.before_cut = Some(Interval {
				start: base.start(),
				end: cut.start().down().unwrap(),
			});
			result.inside_cut = Some(Interval {
				start: cut.start(),
				end: base.end(),
			});
		}
		Config::LeftContainsRight => {
			result.before_cut = Some(Interval {
				start: base.start(),
				end: cut.start().down().unwrap(),
			});
			result.inside_cut = Some(Interval {
				start: cut.start(),
				end: cut.end(),
			});
			//if cut is already max then we don't need to have an
			//after_cut
			if let Some(upped_end) = cut.end().up() {
				result.after_cut = Some(Interval {
					start: upped_end,
					end: base.end(),
				});
			}
		}

		Config::RightFirstNonOverlapping => {
			result.after_cut = Some(Interval {
				start: base.start(),
				end: base.end(),
			});
		}
		Config::RightFirstPartialOverlap => {
			result.after_cut = Some(Interval {
				start: cut.end().up().unwrap(),
				end: base.end(),
			});
			result.inside_cut = Some(Interval {
				start: base.start(),
				end: cut.end(),
			});
		}
		Config::RightContainsLeft => {
			result.inside_cut = Some(Interval {
				start: base.start(),
				end: base.end(),
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
	K: FiniteRange<I>,
{
	range.start() <= range.end()
}

pub(crate) fn overlaps<I, A, B>(a: A, b: B) -> bool
where
	A: FiniteRange<I> + Copy,
	B: FiniteRange<I> + Copy,
	I: Ord,
{
	!matches!(sorted_config(a, b), SortedConfig::NonOverlapping(_, _))
}
