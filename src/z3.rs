use std::fmt;
use std::ffi::{CStr,CString};
use std::ptr;
use std::mem;
use std::str;

use libc;
use z3_sys;

pub struct Z3 {
    ctx: z3_sys::Z3_context
}
#[derive(Clone)]
pub struct Z3Ast<'a> {
    ast: z3_sys::Z3_ast,
    z3: &'a Z3
}
pub struct Z3Model<'a> {
    model: *mut z3_sys::Z3_model,
    res: i32,
    z3: &'a Z3
}

macro_rules! impl_mk_1 {
    ($name:ident, $fun:ident) => (
        pub fn $name<'a>(&'a self, a: &Z3Ast) -> Z3Ast<'a> {
            unsafe {
                let ast = z3_sys::$fun(self.ctx, a.ast);
                Z3Ast {
                    ast: ast,
                    z3: &self
                }
            }
        }
    )
}
macro_rules! impl_mk_2 {
    ($name:ident, $fun:ident) => (
        pub fn $name<'a>(&'a self, t1: &Z3Ast, t2: &Z3Ast) -> Z3Ast<'a> {
            unsafe {
                let ast = z3_sys::$fun(self.ctx, t1.ast, t2.ast);
                Z3Ast {
                    ast: ast,
                    z3: &self
                }
            }
        }
    )
}
macro_rules! impl_mk_3 {
    ($name:ident, $fun:ident) => (
        pub fn $name<'a>(&'a self, t1: &Z3Ast, t2: &Z3Ast, t3: &Z3Ast) -> Z3Ast<'a> {
            unsafe {
                let ast = z3_sys::$fun(self.ctx, t1.ast, t2.ast, t3.ast);
                Z3Ast {
                    ast: ast,
                    z3: &self
                }
            }
        }
    )
}
macro_rules! impl_mk_i_1 {
    ($name:ident, $fun:ident) => (
        pub fn $name<'a>(&'a self, i: u32, t1: &Z3Ast) -> Z3Ast<'a> {
            unsafe {
                let ast = z3_sys::$fun(self.ctx, i, t1.ast);
                Z3Ast {
                    ast: ast,
                    z3: &self
                }
            }
        }
    )
}

impl Z3 {
    pub fn new() -> Z3 {
        unsafe {
            let cfg = z3_sys::Z3_mk_config();
            let ctx = z3_sys::Z3_mk_context(cfg);
            Z3 {
                ctx: ctx
            }
        }
    }
    #[inline]
    pub unsafe fn ctx(&self) -> z3_sys::Z3_context {
        self.ctx
    }
    pub unsafe fn get_model_str(&self, m: z3_sys::Z3_model) -> &str {
        let cstr = z3_sys::Z3_model_to_string(self.ctx, m);
        let slice = CStr::from_ptr(cstr);
        let buf: &[u8] = slice.to_bytes();
        str::from_utf8(buf).unwrap()
    }

    pub fn check_and_get_model<'a>(&'a self, f: &Z3Ast) -> Z3Model<'a> {
        unsafe {
            let m: *mut z3_sys::Z3_model =
                libc::malloc(mem::size_of::<usize>() as libc::size_t)
                as *mut z3_sys::Z3_model;

            z3_sys::Z3_push(self.ctx);
            let not_f = z3_sys::Z3_mk_not(self.ctx, f.ast);
            z3_sys::Z3_assert_cnstr(self.ctx, not_f);

            let res = z3_sys::Z3_check_and_get_model(self.ctx, m);

            z3_sys::Z3_pop(self.ctx, 1);

            Z3Model {
                model: m,
                res: res,
                z3: &self
            }
        }
    }

    //#[deprecated]
    pub fn prove(&self, f: &Z3Ast, is_valid: bool) {
        unsafe {
            z3_sys::Z3_push(self.ctx);
            let not_f = z3_sys::Z3_mk_not(self.ctx, f.ast);
            z3_sys::Z3_assert_cnstr(self.ctx, not_f);

            let m: *mut z3_sys::Z3_model =
                libc::malloc(mem::size_of::<usize>() as libc::size_t)
                as *mut z3_sys::Z3_model;

            match z3_sys::Z3_check_and_get_model(self.ctx, m) {
                z3_sys::Z3_L_FALSE => {
                    /* proved */
                    println!("valid\n");
                    if !is_valid {
                        //exitf("unexpected result");
                    }
                },
                z3_sys::Z3_L_UNDEF => {
                    /* Z3 failed to prove/disprove f. */
                    println!("unknown\n");
                    if *m != ptr::null_mut() {
                        /* m should be viewed as a potential counterexample. */
                        println!("potential counterexample:\n{}\n",
                                 self.get_model_str(*m));
                    }
                    if is_valid {
                        //exitf("unexpected result");
                    }
                },
                z3_sys::Z3_L_TRUE => {
                    /* disproved */
                    println!("invalid\n");
                    if *m != ptr::null_mut() {
                        /* the model returned by Z3 is a counterexample */
                        println!("counterexample:\n{}\n",
                                 self.get_model_str(*m));
                    }
                    if is_valid {
                        //exitf("unexpected result");
                    }
                },
                _ => panic!("not supported")
            }
            if *m != ptr::null_mut() {
                z3_sys::Z3_del_model(self.ctx, *m);
            }
            z3_sys::Z3_pop(self.ctx(), 1);
        }
    }

    impl_mk_2!(eq, Z3_mk_eq);
    impl_mk_2!(div, Z3_mk_div);
    impl_mk_2!(mod_, Z3_mk_mod);
    impl_mk_2!(rem, Z3_mk_rem);
    impl_mk_2!(power, Z3_mk_power);
    impl_mk_2!(lt, Z3_mk_lt);
    impl_mk_2!(le, Z3_mk_le);
    impl_mk_2!(gt, Z3_mk_gt);
    impl_mk_2!(ge, Z3_mk_ge);
    impl_mk_2!(bvand, Z3_mk_bvand);
    impl_mk_2!(bvor, Z3_mk_bvor);
    impl_mk_2!(bvxor, Z3_mk_bvxor);
    impl_mk_2!(bvnand, Z3_mk_bvnand);
    impl_mk_2!(bvnor, Z3_mk_bvnor);
    impl_mk_2!(bvxnor, Z3_mk_bvxnor);
    impl_mk_2!(bvadd, Z3_mk_bvadd);
    impl_mk_2!(bvsub, Z3_mk_bvsub);
    impl_mk_2!(bvmul, Z3_mk_bvmul);
    impl_mk_2!(bvudiv, Z3_mk_bvudiv);
    impl_mk_2!(bvsdiv, Z3_mk_bvsdiv);
    impl_mk_2!(bvurem, Z3_mk_bvurem);
    impl_mk_2!(bvsrem, Z3_mk_bvsrem);
    impl_mk_2!(bvsmod, Z3_mk_bvsmod);
    impl_mk_2!(bvult, Z3_mk_bvult);
    impl_mk_2!(bvslt, Z3_mk_bvslt);
    impl_mk_2!(bvule, Z3_mk_bvule);
    impl_mk_2!(bvsle, Z3_mk_bvsle);
    impl_mk_2!(bvuge, Z3_mk_bvuge);
    impl_mk_2!(bvsge, Z3_mk_bvsge);
    impl_mk_2!(bvugt, Z3_mk_bvugt);
    impl_mk_2!(bvsgt, Z3_mk_bvsgt);
    impl_mk_2!(concat, Z3_mk_concat);
    impl_mk_2!(bvshl, Z3_mk_bvshl);
    impl_mk_2!(bvlshr, Z3_mk_bvlshr);
    impl_mk_2!(bvashr, Z3_mk_bvashr);
    impl_mk_2!(ext_rotate_left, Z3_mk_ext_rotate_left);
    impl_mk_2!(ext_rotate_right, Z3_mk_ext_rotate_right);
    impl_mk_2!(bvadd_no_underflow, Z3_mk_bvadd_no_underflow);
    impl_mk_2!(bvsub_no_overflow, Z3_mk_bvsub_no_overflow);
    impl_mk_2!(bvsdiv_no_overflow, Z3_mk_bvsdiv_no_overflow);
    impl_mk_2!(bvmul_no_underflow, Z3_mk_bvmul_no_underflow);

    impl_mk_1!(not, Z3_mk_not);
    impl_mk_1!(int2real, Z3_mk_int2real);
    impl_mk_1!(real2int, Z3_mk_real2int);
    impl_mk_1!(is_int, Z3_mk_is_int);
    impl_mk_1!(bvnot, Z3_mk_bvnot);
    impl_mk_1!(bvredand, Z3_mk_bvredand);
    impl_mk_1!(bvredor, Z3_mk_bvredor);
    impl_mk_1!(bvneg_no_overflow, Z3_mk_bvneg_no_overflow);
    impl_mk_1!(bvneg, Z3_mk_bvneg);

    impl_mk_i_1!(sign_ext, Z3_mk_sign_ext);
    impl_mk_i_1!(zero_ext, Z3_mk_zero_ext);
    impl_mk_i_1!(repeat, Z3_mk_repeat);
    impl_mk_i_1!(rotate_left, Z3_mk_rotate_left);
    impl_mk_i_1!(rotate_right, Z3_mk_rotate_right);

    impl_mk_3!(ite, Z3_mk_ite);

    /// Extract bits from BitVector
    pub fn extract<'a>(&'a self, high: u32, low: u32, t1: &Z3Ast) -> Z3Ast<'a> {
        unsafe {
            let ast = z3_sys::Z3_mk_extract(self.ctx, high, low, t1.ast);
            Z3Ast {
                ast: ast,
                z3: &self
            }
        }
    }

    /// Create a new BitVector const of name `i` and width `w`
    pub fn mk_bv_i(&self, i: i32, w: u32) -> Z3Ast {
        unsafe {
            let sort= z3_sys::Z3_mk_bv_sort(self.ctx, w);
            let sym = z3_sys::Z3_mk_int_symbol(self.ctx, i);
            Z3Ast {
                ast: z3_sys::Z3_mk_const(self.ctx, sym, sort),
                z3: &self
            }
        }
    }
    /// Create a new BitVector const of name `s` and width `w`
    pub fn mk_bv_str<'a>(&'a self, s: &str, w: u32) -> Z3Ast<'a> {
        unsafe {
            let sort= z3_sys::Z3_mk_bv_sort(self.ctx, w);
            let cs = CString::new(s).unwrap();
            let sym = z3_sys::Z3_mk_string_symbol(self.ctx, cs.as_ptr());
            Z3Ast {
                ast: z3_sys::Z3_mk_const(self.ctx, sym, sort),
                z3: &self
            }
        }
    }

    /// Create a new BitVector const (real const) from Numerical String
    pub fn mk_bv_const_str<'a>(&'a self, s: &str, w: u32) -> Z3Ast<'a> {
        unsafe {
            let sort= z3_sys::Z3_mk_bv_sort(self.ctx, w);
            let cs = CString::new(s).unwrap();

            Z3Ast {
                ast: z3_sys::Z3_mk_numeral(self.ctx, cs.as_ptr(), sort),
                z3: &self
            }
        }
    }

    /// Create a new BitVector const (real const) from i32
    pub fn mk_bv_const_i<'a>(&'a self, i: i32, w: u32) -> Z3Ast<'a> {
        unsafe {
            let sort= z3_sys::Z3_mk_bv_sort(self.ctx, w);
            Z3Ast {
                ast: z3_sys::Z3_mk_int(self.ctx, i, sort),
                z3: &self
            }
        }
    }

    /// Clone AST
    pub fn clone_ast<'a>(&'a self, a: &Z3Ast) -> Z3Ast<'a> {
        Z3Ast {
            ast: a.ast,
            z3: &self
        }
    }
}

impl <'a> Z3Ast<'a> {
    /// Get u64 representation of this Ast value if possible
    pub fn get_u64(&self) -> Option<u64> {
        unsafe {
            let mut res: u64 = 0;
            if z3_sys::Z3_get_numeral_uint64(self.z3.ctx(), self.ast, &mut res)
                == z3_sys::Z3_L_TRUE
            {
                Some(res)
            } else {
                None
            }
        }
    }
    /// Get numeral string representation of this Ast value in base 10
    pub fn get_numstring(&self) -> Option<String> {
        unsafe {
            let cstr = z3_sys::Z3_get_numeral_string(self.z3.ctx(), self.ast);
            let slice = CStr::from_ptr(cstr);
            if let Ok(s) = slice.to_str() {
                Some(s.to_owned())
            } else {
                None
            }

        }
    }
    /// Get BitVector width
    pub fn get_bv_width(&self) -> u32 {
        unsafe {
            let sort = z3_sys::Z3_get_sort(self.z3.ctx(), self.ast);
            let sort_kind = z3_sys::Z3_get_sort_kind(self.z3.ctx(), sort);
            if sort_kind == z3_sys::Z3_BV_SORT {
                z3_sys::Z3_get_bv_sort_size(self.z3.ctx(), sort)
            } else if sort_kind == z3_sys::Z3_BOOL_SORT  {
                1
            } else {
                unreachable!()
            }
        }
    }
    /// Zero extend BitVector
    pub fn zero_ext(&self, i: u32) -> Z3Ast<'a> {
        self.z3.zero_ext(i, &self)
    }
    /// Sign extend BitVector
    pub fn sign_ext(&self, i: u32) -> Z3Ast<'a> {
        self.z3.sign_ext(i, &self)
    }
    /// Extract bits
    pub fn extract(&self, high: u32, low: u32) -> Z3Ast<'a> {
        self.z3.extract(high, low, &self)
    }

    /// Get AST String
    pub fn get_string(&self) -> &str {
        unsafe {
            let cstr = z3_sys::Z3_ast_to_string(self.z3.ctx(), self.ast);
            let slice = CStr::from_ptr(cstr);
            let buf: &[u8] = slice.to_bytes();
            str::from_utf8(buf).unwrap()
        }
    }
}

impl<'a> fmt::Debug for Z3Ast<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({})", self.get_string())
    }
}

impl <'a> Z3Model<'a> {
    pub fn eval(&'a self, ast: &Z3Ast) -> Option<Z3Ast<'a>> {
        if self.is_model() {
            unsafe {
                let mut res_ast: z3_sys::Z3_ast = ptr::null_mut();
                if z3_sys::Z3_model_eval(self.z3.ctx(), *self.model,
                                         ast.ast, z3_sys::Z3_L_TRUE,
                                         &mut res_ast) == z3_sys::Z3_L_TRUE {
                    Some(Z3Ast {
                        ast: res_ast,
                        z3: self.z3
                    })
                } else {
                    None
                }
            }
        } else {
            None
        }
    }

    pub fn is_valid(&self) -> bool { self.res == z3_sys::Z3_L_FALSE }
    pub fn is_model(&self) -> bool {
        match self.res {
            z3_sys::Z3_L_UNDEF | z3_sys::Z3_L_TRUE => true,
            z3_sys::Z3_L_FALSE => false,
            _ => panic!("not supported")
        }
    }

    pub fn get_str(&self) -> &str {
        if self.is_model() {
            unsafe {
                let cstr = z3_sys::Z3_model_to_string(self.z3.ctx(), *self.model);
                let slice = CStr::from_ptr(cstr);
                let buf: &[u8] = slice.to_bytes();
                str::from_utf8(buf).unwrap()
            }
        } else {
            "no model"
        }
    }
}

impl Drop for Z3 {
    fn drop(&mut self) {
        unsafe {
            z3_sys::Z3_del_context(self.ctx);
        }
    }
}

#[test]
fn test_get_bv_width() {
    let z3 = Z3::new();
    let a = z3.mk_bv_i(1, 32);
    let b = z3.mk_bv_str("b", 64);
    let c = z3.mk_bv_str("big", 256);
    let d = z3.mk_bv_i(2, 1);

    assert_eq!(a.get_bv_width(), 32);
    assert_eq!(b.get_bv_width(), 64);
    assert_eq!(c.get_bv_width(), 256);
    assert_eq!(d.get_bv_width(), 1);
}

#[test]
fn test_zero_ext() {
    let z3 = Z3::new();
    let a = z3.mk_bv_str("a", 32);
    let b = a.zero_ext(32);
    assert_eq!(b.get_bv_width(), 64);
}

#[test]
fn test_extract() {
    let z3 = Z3::new();
    let a = z3.mk_bv_const_i(0x1ff00, 32);
    let bits = z3.extract(10, 8, &a);
    let c = z3.mk_bv_const_i(0x7, 3);
    let eq = z3.eq(&c, &bits);
    let model = z3.check_and_get_model(&eq);
    assert!(model.is_valid());
}

/*
//XXX_ should fail?
#[test]
fn test_sdiv() {
   let z3 = Z3::new();
    let aa = z3.mk_bv_const_i(0x1, 1);
    let bb = z3.mk_bv_const_i(0x1, 1);
    let a = aa.sign_ext(127);
    let b = bb.sign_ext(127);
    let c = z3.bvsdiv(&a, &b);
    let res = z3.mk_bv_const_i(20, 1);
    println!("a: {}", a);
    println!("b: {}", b);
    let eq = z3.eq(&c, &res);
    let model = z3.check_and_get_model(&eq);
    assert!(model.is_valid());
}
*/

#[test]
fn it_works() {
    let z3 = Z3::new();
    let a = z3.mk_bv_i(1, 32);
    let b = z3.mk_bv_i(2, 32);
    let c = z3.mk_bv_str("c", 32);

    assert_eq!(c.get_bv_width(), 32);

    let d = z3.bvand(&a, &b);
    let e = z3.bvor(&a, &b);

    //let gt = z3.bvugt(&d, &e);
    let eq = z3.eq(&d, &e);
    //let neq = z3.not(&gt);

    //let h = z3.prove(&eq, true);

    let model = z3.check_and_get_model(&eq);
    println!("model: {}", model.get_str());

    let new_a = model.eval(&a).unwrap();
    let val_a = new_a.get_u64().unwrap();
    println!("val_a: 0x{:x}", val_a);

    let val_a = new_a.get_numstring().unwrap();
    println!("val_a: 0x{}", val_a);

}
