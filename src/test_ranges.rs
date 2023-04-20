use crate::discrete_bounds::{DiscreteBound, DiscreteBounds};
use crate::stepable::Stepable;

pub fn uu() -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Unbounded,
		end: DiscreteBound::Unbounded,
	}
}
pub fn ui(x: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Unbounded,
		end: DiscreteBound::Included(x),
	}
}
pub fn ue(x: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Unbounded,
		end: DiscreteBound::Included(x.down().unwrap()),
	}
}
pub fn iu(x: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Included(x),
		end: DiscreteBound::Unbounded,
	}
}
//fn eu(x: i8) -> TestBounds {
//(Bound::Excluded(x), Bound::Unbounded)
//}
pub fn ii(x1: i8, x2: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Included(x1),
		end: DiscreteBound::Included(x2),
	}
}
pub fn ie(x1: i8, x2: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Included(x1),
		end: DiscreteBound::Included(x2.down().unwrap()),
	}
}
pub fn ei(x1: i8, x2: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Included(x1.up().unwrap()),
		end: DiscreteBound::Included(x2),
	}
}
pub fn ee(x1: i8, x2: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: DiscreteBound::Included(x1.up().unwrap()),
		end: DiscreteBound::Included(x2.down().unwrap()),
	}
}
