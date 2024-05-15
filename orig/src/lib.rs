#![no_std]

use core::ffi::{c_char, c_int, CStr};
#[repr(C)]
pub struct Tcl {
    _data: [u8; 0],
    _marker:
        core::marker::PhantomData<(*mut u8, core::marker::PhantomPinned)>,
}

pub type TclCmdFn = extern "C" fn(*mut Tcl, *mut char, *mut ()) -> c_int;

extern "C" {
    pub fn tcl_eval(tcl: *mut Tcl, s: *const c_char, len: usize) -> c_int;
    pub fn tcl_new() -> *mut Tcl;
    pub fn tcl_destroy(tcl: *mut Tcl);
}

pub struct Handle(*mut Tcl);

pub fn create() -> Handle {
    Handle(unsafe { tcl_new() })
}

impl Handle {
    pub fn eval(&mut self, program: &CStr) -> c_int {
        unsafe {
            tcl_eval(self.0, program.as_ptr(), program.to_bytes().len())
        }
    }
}

impl Drop for Handle {
    fn drop(&mut self) {
        unsafe {
            tcl_destroy(self.0);
        }
    }
}
