
use std::mem::transmute;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

use super::{Abomonation, decode};

/// A type emulating a Vec<T> using an abomonated representation.
pub struct AbomVec<T: Abomonation> {
    roots: Vec<T>,
    bytes: Vec<u8>,
}

impl<T: Abomonation> AbomVec<T> {

}