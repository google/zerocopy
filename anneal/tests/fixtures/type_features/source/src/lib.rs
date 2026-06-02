/// ```lean, anneal
/// instance {N : Std.Usize} : Anneal.IsValid (ConstGen N) where
///   isValid self := N.val > 0
/// ```
struct ConstGen<const N: usize>;

/// ```lean, anneal
/// def isSafe (Self : Type) (N : Std.Usize) : Prop := N.val > 0
/// ```
unsafe trait ConstTrait<const N: usize> {}

unsafe trait AssocType {
    type Item;
}

unsafe impl AssocType for ConstGen<10> {
    type Item = u32;
}

/// ```lean, anneal
/// def isSafe (Self : Type) (inst : UsesAssoc Self) : Prop :=
///   inst.parent_AssocType.Item = Std.U32
/// ```
unsafe trait UsesAssoc: AssocType {}

enum Void {}

/// ```lean, anneal
/// instance : Anneal.IsValid VoidWrapper where
///   isValid self := nomatch self.v0
/// ```
struct VoidWrapper(Void);

enum DataEnum {
    A(u32),
    B { x: u32 },
}

/// ```lean, anneal
/// instance : Anneal.IsValid EnumWrapper where
///   isValid self := match self.v0 with
///     | DataEnum.A _ => True
///     | DataEnum.B _ => False
/// ```
struct EnumWrapper(DataEnum);

/// ```lean, anneal
/// instance : Anneal.IsValid ValidatedEnum where
///   isValid self := match self with
///     | ValidatedEnum.A _ => True
///     | ValidatedEnum.B _ => False
/// ```
enum ValidatedEnum {
    A(u32),
    B { x: u32 },
}
