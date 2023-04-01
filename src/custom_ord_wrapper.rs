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

pub enum CustomOrdWrapper<C, T> {
	CustomOrd(C),
	Value(T),
}

impl<C, T> Ord for CustomOrdWrapper<C, T>
where
	C: Fn(&T) -> Ordering,
{
	fn cmp(&self, other: &Self) -> Ordering {
		match (self, other) {
			(
				CustomOrdWrapper::CustomOrd(custom_ord),
				CustomOrdWrapper::Value(value),
			) => custom_ord(value),
			(
				CustomOrdWrapper::Value(value),
				CustomOrdWrapper::CustomOrd(custom_ord),
			) => custom_ord(value),
			_ => panic!(
				"You must have exactly ONE Value and ONE CustomOrd when comparing CustomOrdWrapper's"
			),
		}
	}
}

impl<C, T> PartialOrd for CustomOrdWrapper<C, T>
where
	C: Fn(&T) -> Ordering,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl<C, T> Eq for CustomOrdWrapper<C, T> where C: Fn(&T) -> Ordering {}

impl<C, T> PartialEq for CustomOrdWrapper<C, T>
where
	C: Fn(&T) -> Ordering,
{
	fn eq(&self, other: &Self) -> bool {
		self.cmp(other).is_eq()
	}
}
