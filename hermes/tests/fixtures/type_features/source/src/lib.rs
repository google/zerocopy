/// ```anneal
/// isValid self := N > 0
/// ```
struct ConstGen<const N: usize>;

/// ```anneal
/// isSafe :
///   N > 0
/// ```
unsafe trait ConstTrait<const N: usize> {}

unsafe trait AssocType {
    type Item;
}

unsafe impl AssocType for ConstGen<10> {
    type Item = u32;
}

/// ```anneal
/// isSafe :
///   AssocType.Item Self = U32
/// ```
unsafe trait UsesAssoc: AssocType {}

enum Void {}

/// ```anneal
/// isValid self := nomatch self
/// ```
struct VoidWrapper(Void);

enum DataEnum {
    A(u32),
    B { x: u32 },
}

/// ```anneal
/// isValid self := match self with | .A _ => True | .B _ => False
/// ```
struct EnumWrapper(DataEnum);

/// ```anneal
/// isValid self := match self with | .A _ => True | .B _ => False
/// ```
enum ValidatedEnum {
    A(u32),
    B { x: u32 },
}
