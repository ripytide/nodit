/*
Copyright 2022,2023 James Forster

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

use core::cmp::Ordering;

use crate::{InclusiveInterval, PointType, RangeType, InclusiveRange};

pub(crate) fn cmp_point_with_range<I, K>(point: I, range: K) -> Ordering
where
	I: PointType,
	K: RangeType<I>,
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
	I: PointType,
	A: RangeType<I>,
	B: RangeType<I>,
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
	NonOverlapping(InclusiveInterval<I>, InclusiveInterval<I>),
	PartialOverlap(InclusiveInterval<I>, InclusiveInterval<I>),
	Swallowed(InclusiveInterval<I>, InclusiveInterval<I>),
}
fn sorted_config<I, A, B>(a: A, b: B) -> SortedConfig<I>
where
	I: PointType,
	A: RangeType<I>,
	B: RangeType<I>,
{
	let ae = InclusiveInterval {
		start: a.start(),
		end: a.end(),
	};
	let be = InclusiveInterval {
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

pub(crate) fn contains_point<I, K>(range: K, point: I) -> bool
where
	I: PointType,
	K: RangeType<I>,
{
	cmp_point_with_range(point, range).is_eq()
}

#[derive(Debug)]
pub(crate) struct CutResult<I> {
	pub(crate) before_cut: Option<InclusiveInterval<I>>,
	pub(crate) inside_cut: Option<InclusiveInterval<I>>,
	pub(crate) after_cut: Option<InclusiveInterval<I>>,
}
pub(crate) fn cut_range<I, A, B>(base: A, cut: B) -> CutResult<I>
where
	I: PointType,
	A: RangeType<I>,
	B: RangeType<I>,
{
	let mut result = CutResult {
		before_cut: None,
		inside_cut: None,
		after_cut: None,
	};

	match config(base, cut) {
		Config::LeftFirstNonOverlapping => {
			result.before_cut = Some(InclusiveInterval {
				start: base.start(),
				end: base.end(),
			});
		}
		Config::LeftFirstPartialOverlap => {
			result.before_cut = Some(InclusiveInterval {
				start: base.start(),
				end: cut.start().down().unwrap(),
			});
			result.inside_cut = Some(InclusiveInterval {
				start: cut.start(),
				end: base.end(),
			});
		}
		Config::LeftContainsRight => {
			result.before_cut = Some(InclusiveInterval {
				start: base.start(),
				end: cut.start().down().unwrap(),
			});
			result.inside_cut = Some(InclusiveInterval {
				start: cut.start(),
				end: cut.end(),
			});
			//if cut is already max then we don't need to have an
			//after_cut
			if let Some(upped_end) = cut.end().up() {
				result.after_cut = Some(InclusiveInterval {
					start: upped_end,
					end: base.end(),
				});
			}
		}

		Config::RightFirstNonOverlapping => {
			result.after_cut = Some(InclusiveInterval {
				start: base.start(),
				end: base.end(),
			});
		}
		Config::RightFirstPartialOverlap => {
			result.after_cut = Some(InclusiveInterval {
				start: cut.end().up().unwrap(),
				end: base.end(),
			});
			result.inside_cut = Some(InclusiveInterval {
				start: base.start(),
				end: cut.end(),
			});
		}
		Config::RightContainsLeft => {
			result.inside_cut = Some(InclusiveInterval {
				start: base.start(),
				end: base.end(),
			});
		}
	}

	//only return valid ranges
	return CutResult {
		before_cut: result.before_cut.filter(|x| x.is_valid()),
		inside_cut: result.inside_cut.filter(|x| x.is_valid()),
		after_cut: result.after_cut.filter(|x| x.is_valid()),
	};
}

pub(crate) fn overlaps<I, A, B>(a: A, b: B) -> bool
where
	I: PointType,
	A: RangeType<I>,
	B: RangeType<I>,
{
	!matches!(sorted_config(a, b), SortedConfig::NonOverlapping(_, _))
}
