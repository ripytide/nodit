use crate::discrete_bounds::DiscreteBounds;
use crate::stepable::Discrete;

pub fn uu() -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: i8::MIN,
		end: i8::MAX,
	}
}
pub fn ui(x: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: i8::MIN,
		end: x,
	}
}
pub fn ue(x: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: i8::MIN,
		end: x.down().unwrap(),
	}
}
pub fn iu(x: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: x,
		end: i8::MAX,
	}
}
//fn eu(x: i8) -> TestBounds {
//(Bound::Excluded(x), Bound::Unbounded)
//}
pub fn ii(x1: i8, x2: i8) -> DiscreteBounds<i8> {
	DiscreteBounds { start: x1, end: x2 }
}
pub fn ie(x1: i8, x2: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: x1.up().unwrap(),
		end: x2.down().unwrap(),
	}
}
pub fn ei(x1: i8, x2: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: x1.up().unwrap(),
		end: x2,
	}
}
pub fn ee(x1: i8, x2: i8) -> DiscreteBounds<i8> {
	DiscreteBounds {
		start: x1.up().unwrap(),
		end: x2.down().unwrap(),
	}
}
