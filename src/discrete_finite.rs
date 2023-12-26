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

//! A module containing the [`DiscreteFinite`] trait and trait impls for the
//! primitive integer datatypes.

/// A trait for things which are both discrete and finite datatypes. See the
/// top-level module documentation for more detailed descriptions on
/// discrete-ness and finite-ness.
pub trait DiscreteFinite {
	/// The minimum value of the type.
	const MIN: Self;
	/// The maximum value of the type.
	const MAX: Self;

	/// The smallest value greater than `self` if one exists.
	fn up(self) -> Option<Self>
	where
		Self: Sized;
	/// The greatest value smaller than `self` if one exists.
	fn down(self) -> Option<Self>
	where
		Self: Sized;
}

macro_rules! foo {
    () => {};
	($ident:ident, $($t:tt)*) => {
		impl DiscreteFinite for $ident {
			const MIN: Self = $ident::MIN;
			const MAX: Self = $ident::MAX;

			fn up(self) -> Option<Self> {
				self.checked_add(1)
			}
			fn down(self) -> Option<Self> {
				self.checked_sub(1)
			}
		}

        foo!($($t)*);
	};
}

foo!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128,);
