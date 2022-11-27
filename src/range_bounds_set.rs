/*
Copyright 2022 James Forster

This file is part of range_bounds_map.

range_bounds_map is free software: you can redistribute it and/or
modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

range_bounds_map is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with range_bounds_map. If not, see <https://www.gnu.org/licenses/>.
*/

use crate::range_bounds_ext::RangeBoundsExt;
use crate::range_bounds_map::RangeBoundsMap;

pub struct RangeBoundsSet<I, K> {
	map: RangeBoundsMap<I, K, ()>,
}

impl<I, K> RangeBoundsSet<I, K>
where
	K: RangeBoundsExt<I>,
	I: Ord + Clone,
{
	pub fn new() -> Self {
		RangeBoundsSet {
			map: RangeBoundsMap::new(),
		}
	}

	//returns Err(()) if the given range overlaps another range
	//does not coalesce ranges if they touch
	pub fn insert(&mut self, range_bounds: K) -> Result<(), ()> {
		self.map.insert(range_bounds, ())
	}

	pub fn overlaps(&self, search_range_bounds: &K) -> bool {
		self.map.overlaps(search_range_bounds)
	}

	pub fn overlapping(
		&self,
		search_range_bounds: &K,
	) -> impl Iterator<Item = &K> {
		self.map
			.overlapping(search_range_bounds)
			.map(|(key, _)| key)
	}

	pub fn get(&self, point: &I) -> Option<&K> {
		self.map.get_key_value(point).map(|(key, _)| key)
	}

	pub fn contains_point(&self, point: &I) -> bool {
		self.map.contains_point(point)
	}

	pub fn iter(&self) -> impl Iterator<Item = &K> {
		self.map.iter().map(|(key, _)| key)
	}
}
