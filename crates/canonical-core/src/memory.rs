use std::ops::{RangeFrom, RangeTo};
use std::hash::Hash;

/// Owned (unique and strong) reference to `data`.
pub struct S<T> {
    data: *mut T,
}

/// Weak reference.
pub struct W<T> {
    ptr: *mut T,
}

/// Weak reference to the contents of a vector.
pub struct WVec<T> {
    ptr: *const [T]
}

impl<T> S<T> {
    /// Consumes `data`, returning a strong reference.
    pub fn new(data: T) -> Self {
        let boxed = Box::new(data);
        Self {
            data: Box::into_raw(boxed),
        }
    }

    /// Create a weak reference.
    pub fn downgrade(&self) -> W<T> {
        W { ptr: self.data }
    }

    /// Borrow the referenced data.
    pub fn borrow(&self) -> &T {
        unsafe { &*self.data }
    }

    /// Mutably borrow the referenced data.
    pub fn borrow_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data }
    }
}

impl<T> W<T> {
    /// Borrow the referenced data.
    pub fn borrow(&self) -> &T {
        unsafe { &*self.ptr }
    }
    
    /// Mutably borrow the referenced data.
    pub fn borrow_mut(&mut self) -> &mut T{
        unsafe { &mut *self.ptr }
    }
    
    /// Determine whether the weak reference points to the data owned by `s`.
    pub fn points_to(&self, s: &S<T>) -> bool {
        self.ptr == s.data
    }

    /// Cast to usize.
    pub(crate) fn usize(&self) -> usize {
        self.ptr as usize
    }
}

impl<T> WVec<T> {
    /// A slice containing all of `v`.
    pub fn new(v: &Vec<T>) -> Self {
        WVec { ptr: v.as_slice() }
    }

    // Convert `slice` into a `WVec`.
    // pub fn from(slice: &[T]) -> Self {
    //     WVec { ptr: slice }
    // }

    // Length of the underlying slice.
    // pub fn len(&self) -> usize {
    //     unsafe { (*self.ptr).len() }
    // }
}

impl<T> std::ops::Index<usize> for WVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { &(*self.ptr)[index] }
    }
}

impl<T> std::ops::Index<RangeFrom<usize>> for WVec<T> {
    type Output = [T];

    fn index(&self, index: RangeFrom<usize>) -> &Self::Output {
        unsafe { &(*self.ptr)[index] }
    }
}

impl<T> std::ops::Index<RangeTo<usize>> for WVec<T> {
    type Output = [T];

    fn index(&self, index: RangeTo<usize>) -> &Self::Output {
        unsafe { &(*self.ptr)[index] }
    }
}

impl<T> Clone for W<T> {
    fn clone(&self) -> Self {
        W { ptr: self.ptr }
    }
}

impl<T> Clone for WVec<T> {
    fn clone(&self) -> Self {
        WVec { ptr: self.ptr }
    }
}

impl<T> Drop for S<T> {
    fn drop(&mut self) {
        unsafe { drop(Box::from_raw(self.data)) }
    }
}

impl<T> PartialEq for W<T> {
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T> Eq for W<T> {}

unsafe impl<T> Send for S<T> {}

impl<T> Hash for W<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ptr.hash(state);
    }
}