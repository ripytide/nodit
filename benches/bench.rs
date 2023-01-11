#![feature(test)]

extern crate test;
use test::Bencher;
extern crate range_bounds_map;
use std::ops::Range;

use range_bounds_map::*;

/// linear multiplier for work done by benchmarks
const REPEAT: usize = 100;

fn build_identity_map(n: usize) -> RangeBoundsMap<usize, Range<usize>, usize> {
	let mut map = RangeBoundsMap::new();
	for i in 0..n {
		if let Err(OverlapError) = map.insert_platonic((2 * i)..(2 * i + 1), i)
		{
			panic!("Failed to insert")
		}
	}
	map
}

#[bench]
fn bench_insert_platonic(b: &mut Bencher) {
	b.iter(|| {
		let mut map = RangeBoundsMap::new();
		for i in 0..REPEAT {
			let r = (2 * i)..(2 * i + 1);
			if let Err(OverlapError) = map.insert_platonic(r, i) {
				panic!("Failed to insert")
			}
		}
	});
}

#[bench]
fn bench_overlaps(b: &mut Bencher) {
	let map = build_identity_map(REPEAT);
	b.iter(|| for _ in map.overlapping(&(0..2 * REPEAT)) {})
}

#[bench]
fn bench_get_entry_at_point(b: &mut Bencher) {
	b.iter(|| {})
}

#[bench]
fn bench_iter(b: &mut Bencher) {
	b.iter(|| {})
}

#[bench]
fn bench_remove_overlapping(b: &mut Bencher) {
	b.iter(|| {})
}

#[bench]
fn bench_cut(b: &mut Bencher) {
	b.iter(|| {})
}

#[bench]
fn bench_gaps(b: &mut Bencher) {
	b.iter(|| {})
}
