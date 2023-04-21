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

pub trait DiscreteFinite {
	const MIN: Self;
	const MAX: Self;

	fn up(self) -> Option<Self>
	where
		Self: Sized;
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
