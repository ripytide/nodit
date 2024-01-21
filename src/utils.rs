/*
Copyright 2022,2023 James Forster

This file is part of nodit.

nodit is free software: you can redistribute it and/or
modify it under the terms of the GNU Affero General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

nodit is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with nodit. If not, see <https://www.gnu.org/licenses/>.
*/

use core::cmp::Ordering;

use crate::{InclusiveInterval, Interval, IntervalType, PointType};

pub(crate) fn cmp_point_with_interval<I, K>(point: I, interval: K) -> Ordering
where
	I: PointType,
	K: IntervalType<I>,
{
	inclusive_comp_generator(point, Ordering::Equal)(&interval)
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
	A: IntervalType<I>,
	B: IntervalType<I>,
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
	I: PointType,
	A: IntervalType<I>,
	B: IntervalType<I>,
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

pub(crate) fn contains_point<I, K>(interval: K, point: I) -> bool
where
	I: PointType,
	K: IntervalType<I>,
{
	cmp_point_with_interval(point, interval).is_eq()
}

#[derive(Debug)]
pub(crate) struct CutResult<I> {
	pub(crate) before_cut: Option<Interval<I>>,
	pub(crate) inside_cut: Option<Interval<I>>,
	pub(crate) after_cut: Option<Interval<I>>,
}
pub(crate) fn cut_interval<I, A, B>(base: A, cut: B) -> CutResult<I>
where
	I: PointType,
	A: IntervalType<I>,
	B: IntervalType<I>,
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

	//only return valid intervals
	return CutResult {
		before_cut: result.before_cut.filter(|x| x.is_valid()),
		inside_cut: result.inside_cut.filter(|x| x.is_valid()),
		after_cut: result.after_cut.filter(|x| x.is_valid()),
	};
}

pub(crate) fn overlaps<I, A, B>(a: A, b: B) -> bool
where
	I: PointType,
	A: IntervalType<I>,
	B: IntervalType<I>,
{
	!matches!(sorted_config(a, b), SortedConfig::NonOverlapping(_, _))
}

pub(crate) fn starts_comp<I, K>() -> impl FnMut(&K, &K) -> Ordering
where
	I: PointType,
	K: IntervalType<I>,
{
	|inner_interval: &K, new_interval: &K| {
		new_interval.start().cmp(&inner_interval.start())
	}
}
pub(crate) fn exclusive_comp_generator<I, K>(
	point: I,
	extraneous_result: Ordering,
) -> impl FnMut(&K) -> Ordering
where
	I: PointType,
	K: IntervalType<I>,
{
	move |inner_interval: &K| {
		if point == inner_interval.start() && point == inner_interval.end() {
			extraneous_result
		} else if point <= inner_interval.start() {
			Ordering::Less
		} else if point >= inner_interval.end() {
			Ordering::Greater
		} else {
			Ordering::Equal
		}
	}
}
pub(crate) fn inclusive_comp_generator<I, K>(
	point: I,
	extraneous_result: Ordering,
) -> impl FnMut(&K) -> Ordering
where
	I: PointType,
	K: IntervalType<I>,
{
	move |inner_interval: &K| {
		if point < inner_interval.start() {
			Ordering::Less
		} else if point > inner_interval.end() {
			Ordering::Greater
		} else {
			extraneous_result
		}
	}
}
pub(crate) fn overlapping_comp<I, K>(point: I) -> impl FnMut(&K) -> Ordering
where
	I: PointType,
	K: IntervalType<I>,
{
	move |inner_interval: &K| cmp_point_with_interval(point, *inner_interval)
}
pub(crate) fn touching_start_comp<I, K>(start: I) -> impl FnMut(&K) -> Ordering
where
	I: PointType,
	K: IntervalType<I>,
{
	move |inner_interval: &K| match inner_interval.end().up() {
		Some(touching_position) => start.cmp(&touching_position),
		None => Ordering::Less,
	}
}
pub(crate) fn touching_end_comp<I, K>(end: I) -> impl FnMut(&K) -> Ordering
where
	I: PointType,
	K: IntervalType<I>,
{
	move |inner_interval: &K| match inner_interval.start().down() {
		Some(touching_position) => end.cmp(&touching_position),
		None => Ordering::Greater,
	}
}

pub(crate) fn invalid_interval_panic<Q, I>(interval: Q)
where
	I: PointType,
	Q: IntervalType<I>,
{
	if !interval.is_valid() {
		panic!(
			"invalid interval given to function see here for more details: https://docs.rs/nodit/latest/nodit/#invalid-intervals"
		);
	}
}
