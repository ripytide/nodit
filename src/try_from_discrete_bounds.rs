use crate::discrete_bounds::DiscreteBound;

pub trait TryFromDiscreteBounds<I> {
	fn try_from_discrete_bounds(
		start: DiscreteBound<I>,
		end: DiscreteBound<I>,
	) -> Result<Self, TryFromDiscreteBoundsError>
	where
		Self: Sized;
}
