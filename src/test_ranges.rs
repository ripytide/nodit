use std::ops::Bound;

pub type TestBounds = (Bound<u8>, Bound<u8>);

#[allow(dead_code)]
pub fn uu() -> TestBounds {
	(Bound::Unbounded, Bound::Unbounded)
}
#[allow(dead_code)]
pub fn ui(x: u8) -> TestBounds {
	(Bound::Unbounded, Bound::Included(x))
}
#[allow(dead_code)]
pub fn ue(x: u8) -> TestBounds {
	(Bound::Unbounded, Bound::Excluded(x))
}
#[allow(dead_code)]
pub fn iu(x: u8) -> TestBounds {
	(Bound::Included(x), Bound::Unbounded)
}
//fn eu(x: u8) -> TestBounds {
//(Bound::Excluded(x), Bound::Unbounded)
//}
#[allow(dead_code)]
pub fn ii(x1: u8, x2: u8) -> TestBounds {
	(Bound::Included(x1), Bound::Included(x2))
}
#[allow(dead_code)]
pub fn ie(x1: u8, x2: u8) -> TestBounds {
	(Bound::Included(x1), Bound::Excluded(x2))
}
#[allow(dead_code)]
pub fn ei(x1: u8, x2: u8) -> TestBounds {
	(Bound::Excluded(x1), Bound::Included(x2))
}
#[allow(dead_code)]
pub fn ee(x1: u8, x2: u8) -> TestBounds {
	(Bound::Excluded(x1), Bound::Excluded(x2))
}

#[allow(dead_code)]
pub fn u() -> Bound<u8> {
	Bound::Unbounded
}
