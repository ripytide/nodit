use std::ops::{Bound, Range};

use range_bounds_set::{range_bounds_set::RangeBoundsSet, range_bounds_ext::RangeBoundsExt};

static NICE_NUMBERS: &'static [u8] = &[2, 4, 6, 8, 10];
type Sim = (Bound<u8>, Bound<u8>);

fn main() {
	println!("Hello, world!");
}

struct OverlapTestCase {
	range_bounds_set: RangeBoundsSet<Sim, u8>,
	overlap_range: Sim,
}

struct OverlapTestCaseWithAnswer {
	test_case: OverlapTestCase,
	answer: Vec<Sim>,
}

fn generate_overlap_test_cases() -> Vec<OverlapTestCase> {
	let mut output = Vec::new();
	//case zero
	for overlap_range in all_sim() {
		output.push(OverlapTestCase {
			range_bounds_set: RangeBoundsSet::new(),
			overlap_range,
		})
	}

	//case one
	for overlap_range in all_sim() {
		for inside_range in all_sim() {
			let mut range_bounds_set = RangeBoundsSet::new();
			range_bounds_set.raw_insert(inside_range);
			output.push(OverlapTestCase {
				range_bounds_set,
				overlap_range,
			})
		}
	}

	//case two

	return output;
}

fn all_valid_sim_pairs() -> Vec<(Sim, Sim)> {
	let mut output = Vec::new();
	for sim1 in all_sim() {
		for sim2 in all_sim() {
			output.push((sim1, sim2));
		}
	}

	output.retain(is_valid_sim_pair);

	return output;
}

fn is_valid_sim_pair((sim1, sim2): &(Sim, Sim)) -> bool {
    //do they overlap?
    if sim1.overlaps(sim2) {
        return false;
    }
    if 

    //is it an exclusive-exclusive with start==end?
}

fn all_sim() -> Vec<Sim> {
	let mut output = Vec::new();

	//bounded-bounded
	for start_bound in all_finite_bounded() {
		for end_bound in all_finite_bounded() {
			output.push((start_bound, end_bound));
		}
	}
	//bounded-unbounded
	for start_bound in all_finite_bounded() {
		output.push((start_bound, Bound::Unbounded));
	}
	//unbounded-bounded
	for end_bound in all_finite_bounded() {
		output.push((Bound::Unbounded, end_bound));
	}
	//bounded-bounded
	output.push((Bound::Unbounded, Bound::Unbounded));
	return output;
}

fn all_finite_bounded() -> Vec<Bound<u8>> {
	let mut output = Vec::new();
	for i in 0..5 {
		for k in 0..=1 {
			output.push(finite_bound(i, k == 0));
		}
	}
	return output;
}

fn finite_bound(x: u8, included: bool) -> Bound<u8> {
	match included {
		true => Bound::Included(x),
		false => Bound::Excluded(x),
	}
}
