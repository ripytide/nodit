use core::cmp::Ordering;

use crate::{InclusiveInterval, Interval, IntervalType, PointType};

pub(crate) fn cmp_point_with_interval<I, K>(point: &I, interval: &K) -> Ordering
where
	I: PointType,
	K: IntervalType<I>,
{
	inclusive_comp_generator(point, Ordering::Equal)(interval)
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
		match (contains_point_by_ref(&a, &b.start()), contains_point_by_ref(&a, &b.end())) {
			(false, false) => Config::LeftFirstNonOverlapping,
			(true, false) => Config::LeftFirstPartialOverlap,
			(true, true) => Config::LeftContainsRight,
			(false, true) => unreachable!(),
		}
	} else {
		match (contains_point_by_ref(&b, &a.start()), contains_point_by_ref(&b, &a.end())) {
			(false, false) => Config::RightFirstNonOverlapping,
			(true, false) => Config::RightFirstPartialOverlap,
			(true, true) => Config::RightContainsLeft,
			(false, true) => unreachable!(),
		}
	}
}

pub(crate) enum SortedConfig<I> {
	NonOverlapping(Interval<I>, Interval<I>),
	PartialOverlap(Interval<I>, Interval<I>),
	Swallowed(Interval<I>, Interval<I>),
}
pub(crate) fn sorted_config<I, A, B>(a: A, b: B) -> SortedConfig<I>
where
	I: PointType,
	A: IntervalType<I>,
	B: IntervalType<I>,
{
	let ae = Interval {
		start: a.start().clone(),
		end: a.end().clone(),
	};
	let be = Interval {
		start: b.start().clone(),
		end: b.end().clone(),
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
	cmp_point_with_interval(&point, &interval).is_eq()
}

pub(crate) fn contains_point_by_ref<I, K>(interval: &K, point: &I) -> bool
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
pub(crate) fn cut_interval<I, A, B>(base: &A, cut: &B) -> CutResult<I>
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

	match config(base.clone(), cut.clone()) {
		Config::LeftFirstNonOverlapping => {
			result.before_cut = Some(Interval {
				start: base.start().clone(),
				end: base.end().clone(),
			});
		}
		Config::LeftFirstPartialOverlap => {
			result.before_cut = Some(Interval {
				start: base.start().clone(),
				end: cut.start().down().unwrap().clone(),
			});
			result.inside_cut = Some(Interval {
				start: cut.start().clone(),
				end: base.end().clone(),
			});
		}
		Config::LeftContainsRight => {
			result.before_cut = Some(Interval {
				start: base.start().clone(),
				end: cut.start().down().unwrap().clone(),
			});
			result.inside_cut = Some(Interval {
				start: cut.start().clone(),
				end: cut.end().clone(),
			});
			//if cut is already max then we don't need to have an
			//after_cut
			if let Some(upped_end) = cut.end().up() {
				result.after_cut = Some(Interval {
					start: upped_end.clone(),
					end: base.end().clone(),
				});
			}
		}

		Config::RightFirstNonOverlapping => {
			result.after_cut = Some(Interval {
				start: base.start().clone(),
				end: base.end().clone(),
			});
		}
		Config::RightFirstPartialOverlap => {
			result.after_cut = Some(Interval {
				start: cut.end().up().unwrap(),
				end: base.end().clone(),
			});
			result.inside_cut = Some(Interval {
				start: base.start().clone(),
				end: cut.end().clone(),
			});
		}
		Config::RightContainsLeft => {
			result.inside_cut = Some(Interval {
				start: base.start().clone(),
				end: base.end().clone(),
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
	point: &I,
	extraneous_result: Ordering,
) -> impl FnMut(&K) -> Ordering + use<'_, I, K>
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
	point: &I,
	extraneous_result: Ordering,
) -> impl FnMut(&K) -> Ordering + use<'_, I, K>
where
	I: PointType,
	K: IntervalType<I>,
{
	move |inner_interval: &K| {
		if point < &inner_interval.start() {
			Ordering::Less
		} else if point > &inner_interval.end() {
			Ordering::Greater
		} else {
			extraneous_result
		}
	}
}
pub(crate) fn overlapping_comp<I, K>(point: &I) -> impl FnMut(&K) -> Ordering + use<'_, I, K>
where
	I: PointType,
	K: IntervalType<I>,
{
	move |inner_interval: &K| cmp_point_with_interval(point, inner_interval)
}
pub(crate) fn touching_start_comp<I, K>(start: &I) -> impl FnMut(&K) -> Ordering + use<'_, I, K>
where
	I: PointType,
	K: IntervalType<I>,
{
	move |inner_interval: &K| match inner_interval.end().up() {
		Some(touching_position) => start.cmp(&touching_position),
		None => Ordering::Less,
	}
}
pub(crate) fn touching_end_comp<I, K>(end: &I) -> impl FnMut(&K) -> Ordering + use<'_, I, K>
where
	I: PointType,
	K: IntervalType<I>,
{
	move |inner_interval: &K| match inner_interval.start().down() {
		Some(touching_position) => end.cmp(&touching_position),
		None => Ordering::Greater,
	}
}

pub(crate) fn invalid_interval_panic<Q, I>(interval: &Q)
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
