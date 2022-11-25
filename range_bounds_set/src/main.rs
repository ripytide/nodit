#![feature(let_chains)]

use std::fmt::Display;
use std::ops::Bound;

use range_bounds_set::range_bounds::RangeBounds;
use range_bounds_set::RangeBoundsSet;

static NICE_NUMBERS: &'static [u8] = &[2, 4, 6, 8, 10];
type TestBounds = (Bound<u8>, Bound<u8>);

fn main() {
	color_backtrace::install();
	for test_case in generate_overlaps_test_cases() {
		println!("{}", test_case);
	}
}

struct OverlapsTestCase {
	range_bounds1: TestBounds,
	range_bounds2: TestBounds,
}
struct OverlapsTestCaseWithAnswer {
	test_case: OverlapsTestCase,
	answer: bool,
}

struct OverlappingTestCase {
	range_bounds_set: RangeBoundsSet<u8, TestBounds>,
	overlap_range: TestBounds,
}
struct OverlappingTestCaseWithAnswer {
	test_case: OverlappingTestCase,
	answer: Vec<TestBounds>,
}

impl Display for OverlapsTestCase {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		writeln!(f, "===  1  2  3  4  5  6  7  8  9  10 ===")?;
		writeln!(f, "{}", display_test_bounds(&self.range_bounds1))?;
		writeln!(f, "{}", display_test_bounds(&self.range_bounds2))?;
		Ok(())
	}
}

impl Display for OverlappingTestCase {
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
	let first_scale = 3;
	let first_offset = 2;

	let second_scale = 3;
	let second_offset = 1;

	let first_unbounded_position = 0;
	let second_unbounded_position = 36;

	let first_symbol_position = inner(&test_bounds.0)
		.map(|x| x * first_scale + first_offset)
		.unwrap_or(first_unbounded_position);

	let second_symbol_position = inner(&test_bounds.1)
		.map(|x| x * second_scale + second_offset)
		.unwrap_or(second_unbounded_position);

	format!(
		"{}{}{}{}",
		" ".repeat(first_symbol_position as usize),
		bound_symbol(&test_bounds.0),
		"-".repeat(
			(second_symbol_position.saturating_sub(first_symbol_position))
				as usize
		),
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

fn generate_overlaps_test_cases() -> Vec<OverlapsTestCase> {
	let mut output = Vec::new();

	for overlap_range in all_valid_test_bounds() {
		for (range_bounds1, range_bounds2) in all_valid_test_bounds_pairs() {
			output.push(OverlapsTestCase {
				range_bounds1,
				range_bounds2,
			})
		}
	}

	return output;
}

fn generate_overlapping_test_cases() -> Vec<OverlappingTestCase> {
	let mut output = Vec::new();
	//case zero
	for overlap_range in all_valid_test_bounds() {
		output.push(OverlappingTestCase {
			range_bounds_set: RangeBoundsSet::new(),
			overlap_range,
		})
	}

	//case one
	for overlap_range in all_valid_test_bounds() {
		for inside_range in all_valid_test_bounds() {
			let mut range_bounds_set = range_bounds_set::RangeBoundsSet::new();
			range_bounds_set.insert(inside_range).unwrap();
			output.push(OverlappingTestCase {
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
			range_bounds_set.insert(test_bounds2).unwrap();
			output.push(OverlappingTestCase {
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
	//unbounded-unbounded
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
	for i in NICE_NUMBERS {
		for k in 0..=1 {
			output.push(finite_bound(*i, k == 0));
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
