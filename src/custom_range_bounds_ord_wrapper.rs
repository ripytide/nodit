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
use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::RangeBounds;

use crate::bound_ord::BoundOrd;

#[derive(Clone)]
pub struct BoundOrdBodge<I> {
    bound_ord: BoundOrd<I>
}

impl<I, K> OrdBodge<K> for BoundOrdBodge<I> {
    fn cmp(&self, other: &K) -> Ordering {
        Ordering::Less
    }
}

pub trait OrdBodge<K> {
	fn cmp(&self, other: &K) -> Ordering;
}

pub enum CustomRangeBoundsOrdWrapper<I, K> {
	RangeBounds(K),
	OrdBodge(Box<dyn OrdBodge<K>>),
    PhantomData(PhantomData<I>)
}

impl<I, K> CustomRangeBoundsOrdWrapper<I, K> {
	//todo rename these after finished
	//re-enable warnings
	//do clippy
	//check doctests
	pub fn rxr(&self) -> &K {
		match self {
			CustomRangeBoundsOrdWrapper::RangeBounds(range_bounds) => {
				return range_bounds;
			}
			_ => panic!("unwrap failed"),
		}
	}

	pub fn rx(self) -> K {
		match self {
			CustomRangeBoundsOrdWrapper::RangeBounds(range_bounds) => {
				return range_bounds;
			}
			_ => panic!("unwrap failed"),
		}
	}
}

impl<I, K> Ord for CustomRangeBoundsOrdWrapper<I, K>
where
	I: Ord,
	K: RangeBounds<I>,
{
	fn cmp(&self, other: &Self) -> Ordering {
		todo!()
	}
}

impl<I, K> PartialOrd for CustomRangeBoundsOrdWrapper<I, K>
where
	I: Ord,
	K: RangeBounds<I>,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl<I, K> Eq for CustomRangeBoundsOrdWrapper<I, K>
where
	I: Ord,
	K: RangeBounds<I>,
{
}

impl<I, K> PartialEq for CustomRangeBoundsOrdWrapper<I, K>
where
	I: Ord,
	K: RangeBounds<I>,
{
	fn eq(&self, other: &Self) -> bool {
		self.cmp(other).is_eq()
	}
}
