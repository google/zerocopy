//! Tests for advanced Anneal framework features, including `isValid`, `unsafe(axiom)`, and configuration-dependent signatures.

pub mod is_valid {
    // Struct for testing IsValid with explicit definition.
    /// ```lean, anneal
    /// def isValid (self : InvalidStruct) : Prop := self.x.val > self.y.val
    /// ```
    pub struct InvalidStruct {
        pub x: u32,
        pub y: u32,
    }

    pub struct ValidStruct {
        pub z: u32,
    }

    /// Triggers allow_sorry on the complex isValid autoParam.
    /// Should emit a single "declaration uses sorry" warning.
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (unprovable_is_valid) (fun ret_ => True) := by
    ///   sorry
    /// ```
    pub fn unprovable_is_valid() -> InvalidStruct {
        InvalidStruct { x: 1, y: 2 }
    }

    /// Should NOT trigger any "declaration uses sorry" because `True` for `ValidStruct` is solved automatically.
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (trivial_is_valid) (fun ret_ => True) := by
    ///   simp_all
    /// ```
    pub fn trivial_is_valid() -> ValidStruct {
        ValidStruct { z: 5 }
    }

    /// Struct for testing IsValid with explicit definition in framework context.
    /// ```lean, anneal
    /// def isValid (self : Positive) : Prop := self.val.val > 0
    /// ```
    pub struct Positive {
        pub val: u32,
    }

    /// Immutable args, returning a value with an implicit bound.
    pub fn immutable_args_return_value(x: Positive) -> Positive {
        x
    }

    /// Mutable arguments and return value with implicit bounds.
    pub fn mutable_args_return_value(x: &mut Positive) -> Positive {
        let val = x.val;
        x.val = 2;
        Positive { val }
    }

    pub fn no_args_no_return() {}

    /// ```lean, anneal, spec
    /// theorem spec (x : Std.U32) (p : Positive) :
    ///   Aeneas.Std.WP.spec (immutable_args_no_return x p) (fun ret_ => True) := by
    ///   trivial
    /// ```
    pub fn immutable_args_no_return(_x: u32, _p: Positive) {}

    pub fn mutable_args_no_return(_x: &mut Positive) {}

    pub fn no_args_return_value() -> Positive {
        Positive { val: 1 }
    }
}

pub mod axioms {
    /// A function verifying that `unsafe(axiom)` blocks correctly parse and redact.
    /// ```lean, anneal, unsafe(axiom)
    /// axiom spec :
    ///   Aeneas.Std.WP.spec (test_axiom_pseudo_name) (fun ret_ => True)
    /// ```
    pub unsafe fn test_axiom_pseudo_name() {}

    /// A function verifying that entirely empty `axiom` blocks compile correctly.
    /// ```lean, anneal, unsafe(axiom)
    /// axiom spec :
    ///   Aeneas.Std.WP.spec (test_empty_axiom) (fun ret_ => True)
    /// ```
    pub unsafe fn test_empty_axiom() {}

    /// Using `unsafe(axiom)` to redact a return value property.
    /// ```lean, anneal, unsafe(axiom)
    /// axiom spec :
    ///   Aeneas.Std.WP.spec (redact_return) (fun ret_ => True)
    /// ```
    pub unsafe fn redact_return() -> i32 {
        1 + 1
    }
}

pub mod signatures {
    /// A struct whose layout changes based on the target OS.
    pub struct Config {
        #[cfg(target_os = "linux")]
        pub fd: i32,
        #[cfg(target_os = "windows")]
        pub handle: i32,
    }

    /// Verifying that padded signatures (due to `cfg`) don't break Anneal specs.
    /// ```lean, anneal, spec
    /// theorem spec :
    ///   Aeneas.Std.WP.spec (padded_signature_spec) (fun ret_ => True) := by
    ///   sorry
    /// ```
    pub fn padded_signature_spec() {}
}

pub mod visibility {
    /// ```lean, anneal, spec
    /// theorem spec (x : Std.U32) (_y : Std.U32) (h_eq : x = _y) :
    ///   Aeneas.Std.WP.spec (named_precondition_visibility x _y) (fun ret_ => ret_ = _y) := by
    ///   unfold framework.visibility.named_precondition_visibility at *
    ///   have h := h_eq
    ///   simp_all
    /// ```
    /// Note: `unfold` needs the full path in the spec.
    pub unsafe fn named_precondition_visibility(x: u32, _y: u32) -> u32 {
        x
    }
}

fn clean() {}

/// ```lean, anneal
/// ```
fn _anneal_dummy_1() {}

/// ```lean, anneal
/// proof (h_progress):
///   sorry
/// proof context:
///   have h_foo : True := True.intro
/// ```
pub fn dummy_anneal_padding_9() {}

/// ```lean, anneal
/// ```
fn my_func() {}

fn keep() {}

/// ```lean, anneal
/// ```
fn _anneal_dummy_2() {}

fn code() {}

/// ```lean, anneal
/// ```
fn _anneal_dummy_3() {}

/// ```lean, anneal
/// ```
fn private_helper() {}

