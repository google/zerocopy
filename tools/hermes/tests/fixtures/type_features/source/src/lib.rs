/// ```hermes
/// isValid self := {N} > 0
/// ```
struct ConstGen<const N: usize>;

/// ```hermes
/// isSafe Self := {N} > 0
/// ```
unsafe trait ConstTrait<const N: usize> {}

unsafe trait AssocType {
    type Item;
}

unsafe impl AssocType for ConstGen<10> {
    type Item = u32;
}

/// ```hermes
/// isSafe Self := AssocType.Item Self = U32
/// ```
unsafe trait UsesAssoc: AssocType {}

enum Void {}

/// ```hermes
/// isValid nomatch self
/// ```
struct VoidWrapper(Void);

enum DataEnum {
    A(u32),
    B { x: u32 },
}

/// ```hermes
/// isValid match self with | .A _ => True | .B _ => False
/// ```
struct EnumWrapper(DataEnum);

/// ```hermes
/// isValid match self with | .A _ => True | .B _ => False
/// ```
enum ValidatedEnum {
    A(u32),
    B { x: u32 },
}

union MyUnion {
    f1: u32,
    f2: f32,
}

/// ```hermes
/// isValid True
/// ```
struct UnionWrapper(MyUnion);
