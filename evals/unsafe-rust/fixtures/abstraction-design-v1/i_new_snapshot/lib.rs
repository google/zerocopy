#![allow(dead_code)]

use core::marker::PhantomData;

pub struct View<'a, T> {
    ptr: *mut T,
    borrow: PhantomData<&'a mut T>,
}

impl<'a, T> View<'a, T> {
    pub fn new(value: &'a mut T) -> Self {
        Self { ptr: value, borrow: PhantomData }
    }

    pub fn get(&self) -> &'a T {
        unsafe { &*self.ptr }
    }

    pub fn get_mut(&mut self) -> &'a mut T {
        unsafe { &mut *self.ptr }
    }
}

