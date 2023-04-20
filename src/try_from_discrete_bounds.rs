use crate::{discrete_bounds::DiscreteBounds, TryFromDiscreteBoundsError};

pub trait TryFromDiscreteBounds<I> {
	fn try_from_discrete_bounds(
		discrete_bounds: DiscreteBounds<I>,
	) -> Result<Self, TryFromDiscreteBoundsError>
	where
		Self: Sized;
}
