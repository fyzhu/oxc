#![allow(clippy::inline_always)]

use crate::{Allocator, Box};

pub trait FromIn<'a, T> {
    fn from_in(value: T, alloc: &'a Allocator) -> Self;
}

pub trait IntoIn<'a, T> {
    fn into_in(self, alloc: &'a Allocator) -> T;
}

/// `FromIn` is reflective
impl<'a, T> FromIn<'a, T> for T {
    #[inline(always)]
    fn from_in(t: T, _: &'a Allocator) -> T {
        t
    }
}

/// `FromIn` implicitly implements `IntoIn`.
impl<'a, T, U> IntoIn<'a, U> for T
where
    U: FromIn<'a, T>,
{
    #[inline]
    fn into_in(self, alloc: &'a Allocator) -> U {
        U::from_in(self, alloc)
    }
}

// ---------------- Primitive allocations ----------------

impl<'a> FromIn<'a, String> for crate::String<'a> {
    #[inline(always)]
    fn from_in(value: String, alloc: &'a Allocator) -> Self {
        crate::String::from_str_in(value.as_str(), alloc)
    }
}

impl<'a> FromIn<'a, String> for &'a str {
    #[inline(always)]
    fn from_in(value: String, alloc: &'a Allocator) -> Self {
        crate::String::from_str_in(value.as_str(), alloc).into_bump_str()
    }
}

impl<'a, T> FromIn<'a, T> for Box<'a, T> {
    #[inline(always)]
    fn from_in(value: T, alloc: &'a Allocator) -> Self {
        Box::new_in(value, alloc)
    }
}

impl<'a, T> FromIn<'a, Option<T>> for Option<Box<'a, T>> {
    #[inline(always)]
    fn from_in(value: Option<T>, alloc: &'a Allocator) -> Self {
        value.map(|it| Box::new_in(it, alloc))
    }
}
