#![feature(let_chains)]

use std::fmt::Display;
use std::ops::Bound;

use range_bounds_set::range_bounds::RangeBounds;
use range_bounds_set::RangeBoundsSet;

static NICE_NUMBERS: &'static [u8] = &[2, 4, 6, 8, 10];
type TestBounds = (Bound<u8>, Bound<u8>);

fn main() {
    //pretty_trace::PrettyTrace::new().on();
    color_backtrace::install();
	for test_case in generate_overlap_test_cases() {
		println!("{}", test_case);
	}
}

struct OverlapTestCase {
	range_bounds_set: RangeBoundsSet<u8, TestBounds>,
	overlap_range: TestBounds,
}

impl Display for OverlapTestCase {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let range_bounds_iterator = self.range_bounds_set.iter();

		writeln!(f, "=== 1 2 3 4 5 6 7 8 9 10 ===")?;

		for range_bounds in range_bounds_iterator {
			writeln!(f, "{}", display_test_bounds(range_bounds))?;
		}

		writeln!(f)?;

		writeln!(f, "Overlapping:")?;
		writeln!(f, "{}", display_test_bounds(&self.overlap_range))?;

		Ok(())
	}
}

fn display_test_bounds(test_bounds: &TestBounds) -> String {
	let first_symbol_position = inner(&test_bounds.0).unwrap_or(&0);
	let second_symbol_position = inner(&test_bounds.1).unwrap_or(&16);
	format!(
		"{}{}{}{}",
		" ".repeat(*first_symbol_position as usize),
		bound_symbol(&test_bounds.0),
		"-".repeat(*second_symbol_position as usize),
		bound_symbol(&test_bounds.1)
	)
}

fn bound_symbol(bound: &Bound<u8>) -> String {
	match bound {
		Bound::Included(_) => "⬤".to_string(),
		Bound::Excluded(_) => "○".to_string(),
		Bound::Unbounded => "∞".to_string(),
	}
}

struct OverlapTestCaseWithAnswer {
	test_case: OverlapTestCase,
	answer: Vec<TestBounds>,
}

fn generate_overlap_test_cases() -> Vec<OverlapTestCase> {
	let mut output = Vec::new();
	//case zero
	for overlap_range in all_valid_test_bounds() {
		output.push(OverlapTestCase {
			range_bounds_set: RangeBoundsSet::new(),
			overlap_range,
		})
	}

	//case one
	for overlap_range in all_valid_test_bounds() {
		for inside_range in all_valid_test_bounds() {
			let mut range_bounds_set = range_bounds_set::RangeBoundsSet::new();
			range_bounds_set.insert(inside_range).unwrap();
			output.push(OverlapTestCase {
				range_bounds_set,
				overlap_range,
			})
		}
	}

	//case two
	for overlap_range in all_valid_test_bounds() {
		for (test_bounds1, test_bounds2) in all_valid_test_bounds_pairs() {
			let mut range_bounds_set = range_bounds_set::RangeBoundsSet::new();
			range_bounds_set.insert(test_bounds1).unwrap();
            dbg!(test_bounds2);
			range_bounds_set.insert(test_bounds2).unwrap();
			output.push(OverlapTestCase {
				range_bounds_set,
				overlap_range,
			})
		}
	}

	return output;
}

fn all_valid_test_bounds_pairs() -> Vec<(TestBounds, TestBounds)> {
	let mut output = Vec::new();
	for test_bounds1 in all_valid_test_bounds() {
		for test_bounds2 in all_valid_test_bounds() {
			output.push((test_bounds1, test_bounds2));
		}
	}

	output.retain(is_valid_test_bounds_pair);

	return output;
}

fn is_valid_test_bounds_pair(
	(test_bounds1, test_bounds2): &(TestBounds, TestBounds),
) -> bool {
	//do they overlap?
	!test_bounds1.overlaps(test_bounds2)
}

fn all_valid_test_bounds() -> Vec<TestBounds> {
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

	output.retain(is_valid_test_bounds);
	return output;
}

fn is_valid_test_bounds(test_bounds: &TestBounds) -> bool {
	//the one exception for zero ranges
	if let Bound::Included(start) = test_bounds.0 && let Bound::Included(end) = test_bounds.1 && start==end {
        return true;
    }
	match inner(&test_bounds.0) {
		Some(start) => match inner(&test_bounds.1) {
			Some(end) => start < end,
			None => true,
		},
		None => true,
	}
}

fn inner(bound: &Bound<u8>) -> Option<&u8> {
	match bound {
		Bound::Included(point) => Some(point),
		Bound::Excluded(point) => Some(point),
		Bound::Unbounded => None,
	}
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
