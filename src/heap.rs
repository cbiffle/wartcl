#![warn(unsafe_op_in_unsafe_fn)]

extern crate alloc;

use core::{cell::Cell, cmp::Ordering, fmt::{self, Debug}, hash::{Hash, Hasher}, mem, ops::{Bound, Deref, RangeBounds}, ptr::NonNull};
use alloc::boxed::Box;
use alloc::vec::Vec;

/// Shared control block for a single allocation, allocated separately on the
/// heap. This will live until its refcount reaches zero, at which point it will
/// be deallocated, taking the allocation with it.
struct Shared {
    /// The number of outstanding references.
    refcount: Cell<usize>,
    /// The thing we're referencing
    kind: SharedKind,
}

enum SharedKind {
    Owned(Box<[u8]>),
    Sub {
        owner: Option<NonNull<Shared>>,
        base: NonNull<u8>,
        len: usize,
    },
}

impl Shared {
    fn new_owned(allocation: Box<[u8]>) -> Box<Self> {
        debug_assert!(!allocation.is_empty());
        Box::new(Self {
            refcount: Cell::new(1),
            kind: SharedKind::Owned(allocation),
        })
    }
    fn new_static(data: &'static [u8]) -> Box<Self> {
        debug_assert!(!data.is_empty());
        Box::new(Self {
            refcount: Cell::new(1),
            kind: SharedKind::Sub {
                owner: None,
                base: unsafe { NonNull::new_unchecked(data.as_ptr() as *mut u8) },
                len: data.len(),
            },
        })
    }

    fn len(&self) -> usize {
        match &self.kind {
            SharedKind::Owned(b) => b.len(),
            SharedKind::Sub { len, .. } => *len,
        }
    }

}


/// A reference to a shared value.
pub struct Val(Option<NonNull<Shared>>);

impl Val {
    /// Creates a new empty `Val`. The result won't be associated with any
    /// backing memory, so this operation is essentially free.
    pub const fn new() -> Self {
        Self(None)
    }

    /// Allocates a new block of memory to contain the bytes referenced by
    /// `value`, and then returns a `Val` spanning all of it.
    ///
    /// If `value` is empty, this is equivalent to `Val::new()`.
    pub fn copy(value: &[u8]) -> Self {
        if value.is_empty() {
            Self::new()
        } else {
            let allocation = value.into();
            let mut new_control = Shared::new_owned(allocation);

            Self(Some(unsafe { NonNull::new_unchecked(Box::into_raw(new_control)) }))
        }
    }

    pub fn from_static(slice: &'static [u8]) -> Self {
        if slice.is_empty() {
            Self::new()
        } else {
            let mut new_control = Shared::new_static(slice);

            Self(Some(unsafe { NonNull::new_unchecked(Box::into_raw(new_control)) }))
        }
    }

    fn control(&self) -> Option<&Shared> {
        self.0.map(|p| unsafe { p.as_ref() })
    }

    /*

    /// Returns a new `Val` containing the first `n` bytes referenced by `this`,
    /// while adjusting `this` to omit them.
    ///
    /// This is sort of like `split`, but is slightly cheaper since it reduces
    /// reference count updates.
    ///
    /// `Val::take_first_n(&mut v, 0)` is a weird way of writing `Val::new()`.
    pub fn take_first_n(this: &mut Val, n: usize) -> Self {
        if n == 0 {
            return Self::new();
        }

        let Some(control) = this.control() else {
            panic!();
        };
        if n == control.len() {
            return mem::take(this);
        }

        assert!(n <= control.len());

        let mut first = this.clone();
        first.len = n;

        this.len -= n;
        this.base = unsafe { NonNull::new_unchecked(this.base.as_ptr().add(n)) };

        first
    }
    */

    /// Returns a new `Val` referencing a sub-range of `this`.
    ///
    /// `Val::slice(&v, ..)` is equivalent to `v.clone()`.
    ///
    /// As always, if the result is empty, it doesn't reference backing memory.
    ///
    /// # Panics
    ///
    /// If `range` is out of bounds for `this`.
    pub fn slice(this: &Val, range: impl RangeBounds<usize>) -> Self {
        let start = match range.start_bound() {
            Bound::Included(&i) => i,
            Bound::Excluded(&i) => i + 1,
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(&i) => i + 1,
            Bound::Excluded(&i) => i,
            Bound::Unbounded => this.len(),
        };
        assert!(start <= end);
        assert!(end <= this.len());

        if end == start {
            return Self::new();
        } else if start == 0 && end == this.len() {
            return this.clone();
        }

        let control = unsafe { this.0.unwrap().as_mut() };
        let new_kind = match &control.kind {
            SharedKind::Owned(b) => {
                control.refcount.set(control.refcount.get() + 1);
                SharedKind::Sub {
                    owner: Some(this.0.unwrap()),
                    base: unsafe { NonNull::new_unchecked(b.as_ptr().add(start) as *mut u8) },
                    len: end - start,
                }
            }
            SharedKind::Sub { owner: Some(o), base, .. } => {
                let oref = unsafe { o.as_ref() };
                oref.refcount.set(oref.refcount.get() + 1);
                SharedKind::Sub {
                    owner: Some(*o),
                    base: unsafe { NonNull::new_unchecked(base.as_ptr().add(start)) },
                    len: end - start,
                }
            }
            SharedKind::Sub { owner: None, base, .. } => {
                // No refcount management is needed.
                SharedKind::Sub {
                    owner: None,
                    base: unsafe { NonNull::new_unchecked(base.as_ptr().add(start)) },
                    len: end - start,
                }
            }
        };
        let new_control = Box::new(Shared {
            refcount: Cell::new(1),
            kind: new_kind,
        });

        Self(Some(unsafe { NonNull::new_unchecked(Box::into_raw(new_control)) }))
    }

    pub fn slice_ref(this: &Val, slice: &[u8]) -> Self {
        if slice.is_empty() {
            return Self::new();
        }
        let valid_range = this.as_ptr_range();
        let base = slice.as_ptr();
        let end = unsafe { slice.as_ptr().add(slice.len()) };
        assert!(valid_range.contains(&base) && end <= valid_range.end);

        let control = unsafe { this.0.unwrap().as_mut() };
        let new_owner = match &control.kind {
            SharedKind::Owned(b) => {
                if b.as_ptr() == slice.as_ptr() && b.len() == slice.len() {
                    return this.clone();
                }
                control.refcount.set(control.refcount.get() + 1);
                Some(NonNull::from(control))
            }
            SharedKind::Sub { owner: Some(o), .. } => {
                let oref = unsafe { o.as_ref() };
                oref.refcount.set(oref.refcount.get() + 1);
                Some(*o)
            }
            SharedKind::Sub { owner: None, .. } => {
                None
            }
        };

        let new_control = Box::new(Shared {
            refcount: Cell::new(1),
            kind: SharedKind::Sub {
                owner: new_owner,
                base: unsafe { NonNull::new_unchecked(base as *mut u8) },
                len: slice.len(),
            }
        });

        Self(Some(unsafe { NonNull::new_unchecked(Box::into_raw(new_control)) }))
    }
    /*

    /// Returns the last byte in the slice, simultaneously shortening the slice
    /// by one byte. If the slice is empty, returns `None`.
    ///
    /// If the slice becomes empty, this may cause deallocation of the backing
    /// memory if this is the last reference to it.
    pub fn pop_last(this: &mut Val) -> Option<u8> {
        if this.len == 0 {
            None
        } else {
            let result = unsafe { *this.base.as_ptr().add(this.len - 1) };
            this.len -= 1;
            if this.len == 0 {
                unsafe { this.decrement_ref(); }
            }
            Some(result)
        }
    }


    /// Returns the first byte in teh slice, simultaneously moving the slice's
    /// base address up to exclude it (and reducing the length). If the slice is
    /// empty, returns `None`.
    ///
    /// If the slice becomes empty, this may cause deallocation of the backing
    /// memory if this is the last reference to it.
    pub fn pop_front(this: &mut Val) -> Option<u8> {
        if this.len == 0 {
            None
        } else {
            let result = *unsafe { this.base.as_ref() };
            this.base = unsafe { NonNull::new_unchecked(this.base.as_ptr().add(1)) };
            this.len -= 1;
            if this.len == 0 {
                unsafe { this.decrement_ref(); }
            }
            Some(result)
        }
    }
    */

    /// Decrements the reference count of the control block, if any, and zeroes
    /// the control block pointer.
    ///
    /// # Safety
    ///
    /// This may leave `self`'s internal pointers pointing to a freed chunk of
    /// memory. This is safe if they won't be used again. Two common cases where
    /// this is safe:
    ///
    /// 1. `self` has just become empty (`len == 0`), so it no longer references
    ///    backing memory, and we want the control pointer cleared.
    /// 2. `self` is being dropped, so it doesn't matter what its pointers
    ///    contain because we won't dereference them again.
    unsafe fn decrement_ref(&mut self) {
        if let Some(control) = self.control() {
            let refcount = control.refcount.get();
            if refcount == 1 {
                let boxed_control = unsafe {
                    Box::from_raw(self.0.take().unwrap().as_ptr())
                };
                drop(boxed_control);
            } else {
                control.refcount.set(refcount - 1);
            }
        }
    }
}

/// Creates a `Val` referencing a static byte slice. `Val`s created in this way
/// don't maintain a reference count, and can be cheaply copied or sliced.
impl From<&'static [u8]> for Val {
    fn from(value: &'static [u8]) -> Self {
        Self::from_static(value)
    }
}

/// Creates a `Val` referencing the UTF-8 representation of a static `str`.
/// `Val`s created in this way don't maintain a reference count, and can be
/// cheaply copied or sliced.
impl From<&'static str> for Val {
    fn from(value: &'static str) -> Self {
        Self::from_static(value.as_bytes())
    }
}

/// Converts a vector into a `Val` containing the same bytes, avoiding
/// allocation if possible.
///
/// This will shed excess capacity from the `Vec`. If the `Vec` had excess
/// capacity, this will involve an allocation and copy.
impl From<Vec<u8>> for Val {
    fn from(value: Vec<u8>) -> Self {
        Self::from(value.into_boxed_slice())
    }
}

/// Converts a boxed byte slice into a `Val`, reusing the allocation.
impl From<Box<[u8]>> for Val {
    fn from(value: Box<[u8]>) -> Self {
        if value.is_empty() {
            Self::new()
        } else {
            let new_control = Shared::new_owned(value);

            Self(Some(unsafe { NonNull::new_unchecked(Box::into_raw(new_control)) }))
        }
    }
}

/// Compares the bytes contained in two `Val`s.
///
/// Two `Val`s will compare as equal if they are the same length and reference
/// identical bytes, even if they refer to different backing memory.
impl PartialEq for Val {
    fn eq(&self, other: &Self) -> bool {
        (*self).deref() == (*other).deref()
    }
}

/// Compares the bytes contained in two `Val`s.
///
/// Two `Val`s will compare as equal if they are the same length and reference
/// identical bytes, even if they refer to different backing memory.
impl Eq for Val {}

/// Compares the bytes contained in two `Val`s for ordering.
///
/// The ordering behavior matches `&[u8]`.
impl Ord for Val {
    fn cmp(&self, other: &Self) -> Ordering {
        (*self).deref().cmp(other)
    }
}

/// Compares the bytes contained in two `Val`s for ordering.
///
/// The ordering behavior matches `&[u8]`.
impl PartialOrd for Val {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Debug for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self).deref().fmt(f)
    }
}

impl Hash for Val {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (*self).deref().hash(state)
    }
}

impl Default for Val {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for Val {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        if let Some(control) = self.control() {
            match &control.kind {
                SharedKind::Owned(b) => &*b,
                SharedKind::Sub { base, len, .. } => {
                    unsafe {
                        core::slice::from_raw_parts(base.as_ptr(), *len)
                    }
                }
            }
        } else {
            &[]
        }
    }
}

impl Clone for Val {
    fn clone(&self) -> Self {
        if let Some(control) = self.control() {
            control.refcount.set(control.refcount.get() + 1);
            Self(Some(NonNull::from(control)))
        } else {
            Self::new()
        }
    }
}

impl Drop for Val {
    fn drop(&mut self) {
        unsafe {
            self.decrement_ref();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[track_caller]
    #[allow(useless_ptr_null_checks)]
    fn checks(v: &Val) {
        if let Some(p) = v.0 {
            assert_ne!(v.len(), 0);

            let align = mem::align_of::<Shared>();
            assert_eq!((p.as_ptr() as usize) & (align - 1), 0,
                "control pointer must be properly aligned");
            let c = unsafe { p.as_ref() };
            
            assert!(c.refcount.get() > 0);

            match &c.kind {
                SharedKind::Owned(b) => {
                    assert!(b.len() > 0);
                }
                SharedKind::Sub { owner: Some(o), base, len } => {
                    let oref = unsafe { o.as_ref() };
                    match &oref.kind {
                        SharedKind::Owned(b) => {
                            let valid_range = b.as_ptr_range();
                            assert!(valid_range.contains(&(base.as_ptr() as *const u8)));
                            assert!(unsafe { base.as_ptr().add(*len) } as *const u8 <= valid_range.end);
                        }
                        SharedKind::Sub { .. } => {
                            panic!("double indirection in control block");
                        }
                    }
                }
                SharedKind::Sub { owner: None, base, len } => {
                    assert!((base.as_ptr() as usize).checked_add(*len).is_some());
                }
            }
        } else {
            assert_eq!(v.len(), 0);
        }
    }

    #[track_caller]
    fn assert_refcount_is(v: &Val, n: usize) {
        let control = v.0.expect("value has no control block (static?)");
        let control = unsafe { control.as_ref() };
        
        assert_eq!(control.refcount.get(), n);
    }

    #[test]
    fn new_does_not_allocate() {
        let v = Val::new();

        assert_eq!(v.0, None);
        checks(&v);
    }

    #[test]
    fn empty_slice_copy_does_not_allocate() {
        let v = Val::copy(&[][..]);

        assert_eq!(v.0, None);
        checks(&v);
    }

    #[test]
    fn from_static_does_not_allocate() {
        let v = Val::from_static(b"hello world");
        assert_eq!(v.len(), b"hello world".len());
        checks(&v);
    }

    #[test]
    fn clone_static_does_not_allocate() {
        let v = Val::from_static(b"hello world");
        let v2 = v.clone();

        assert_eq!(v, v2);
        checks(&v);
        checks(&v2);
    }

    #[test]
    fn allocate_slice_copy() {
        let v = Val::copy(b"hello world");
        assert_ne!(v.0, None);
        checks(&v);
        assert_refcount_is(&v, 1);
    }

    #[test]
    fn clone_non_static() {
        let v = Val::copy(b"hello world");
        checks(&v);

        let v2 = v.clone();
        checks(&v);
        checks(&v2);

        assert_eq!(v, v2);

        assert_eq!(v.0, v2.0);
        assert_refcount_is(&v, 2);
        assert_refcount_is(&v2, 2);

        drop(v);
        checks(&v2);
        assert_refcount_is(&v2, 1);
    }

    #[test]
    fn slice() {
        let v = Val::copy(b"hello, world");
        let v_all = Val::slice(&v, 0..);
        checks(&v_all);
        assert_eq!(v, v_all);
        assert_eq!(v.0, v_all.0);
        assert_refcount_is(&v, 2);
        assert_refcount_is(&v_all, 2);

        let v_front = Val::slice(&v, ..5);
        checks(&v_front);
        assert_eq!(&*v_front, b"hello");
        assert_refcount_is(&v, 3);
        assert_refcount_is(&v_all, 3);
        assert_refcount_is(&v_front, 1);

        let v_mid = Val::slice(&v, 1..5);
        checks(&v_mid);
        assert_eq!(&*v_mid, b"ello");
        assert_refcount_is(&v, 4);
        assert_refcount_is(&v_front, 1);
        assert_refcount_is(&v_mid, 1);

        let v_back = Val::slice(&v, 7..);
        checks(&v_back);
        assert_eq!(&*v_back, b"world");
        assert_refcount_is(&v, 5);
        assert_refcount_is(&v_front, 1);
        assert_refcount_is(&v_mid, 1);
        assert_refcount_is(&v_back, 1);

        let v_empty = Val::slice(&v, 5..5);
        checks(&v_empty);
        assert_eq!(&*v_empty, b"");
        // Should not increase refcount:
        assert_refcount_is(&v, 5);
    }

    #[test]
    #[should_panic]
    fn slice_start_out_of_range() {
        Val::slice(&Val::copy(b"hello, world"), 30..);
    }

    #[test]
    #[should_panic]
    fn slice_start_out_of_range2() {
        Val::slice(&Val::copy(b"hello, world"), 30..50);
    }

    #[test]
    #[should_panic]
    fn slice_end_out_of_range() {
        Val::slice(&Val::copy(b"hello, world"), ..30);
    }

    #[test]
    #[should_panic]
    fn slice_end_out_of_range2() {
        Val::slice(&Val::copy(b"hello, world"), 10..30);
    }

    #[test]
    fn slice_ref_allocated() {
        let v = Val::copy(b"hello, world");
        let sub = &v[3..5];
        let v2 = Val::slice_ref(&v, sub);
        checks(&v2);

        assert_eq!(&v2[..], sub);
    }

    #[test]
    fn slice_ref_static() {
        let v = Val::from_static(b"hello, world");
        let sub = &v[3..5];
        let v2 = Val::slice_ref(&v, sub);
        checks(&v2);

        assert_eq!(&v2[..], sub);
    }
}
