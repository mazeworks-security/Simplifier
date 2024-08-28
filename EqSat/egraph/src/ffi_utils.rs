use libc::c_char;
use std::ffi::{CStr, CString};

pub fn marshal_string(s: *const c_char) -> String {
    let c_str = unsafe {
        assert!(!s.is_null());

        CStr::from_ptr(s)
    };

    return c_str.to_str().unwrap().to_string();
}
