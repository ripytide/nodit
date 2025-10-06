//! A module containing the [`DiscreteFinite`] trait and trait impls for the
//! primitive integer datatypes.

/// A trait for things which are both discrete and finite datatypes. See the
/// top-level module documentation for more detailed descriptions on
/// discrete-ness and finite-ness.
pub trait DiscreteFinite {
	/// The minimum value of the type. Kept as function since that allows
	/// complex shared points, keys that have to initialize OnceLock etc.
	fn min_value() -> Self;
	/// The maximum value of the type.
	fn max_value() -> Self;

	/// The smallest value greater than `self` if one exists.
	fn up(&self) -> Option<Self>
	where
		Self: Sized;
	/// The greatest value smaller than `self` if one exists.
	fn down(&self) -> Option<Self>
	where
		Self: Sized;
}

macro_rules! foo {
    () => {};
	($ident:ident, $($t:tt)*) => {
		impl DiscreteFinite for $ident {
			fn min_value () -> Self { $ident::MIN }
			fn max_value () -> Self { $ident::MAX }

			fn up(&self) -> Option<Self> {
				self.checked_add(1)
			}
			fn down(&self) -> Option<Self> {
				self.checked_sub(1)
			}
		}

        foo!($($t)*);
	};
}

foo!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize,);
