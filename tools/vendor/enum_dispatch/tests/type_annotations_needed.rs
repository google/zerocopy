use enum_dispatch::enum_dispatch;

struct HasMany<T, Q>(T, Q);
struct HasSome<T>(T);
struct HasNothing;

#[enum_dispatch]
trait OptionMethods<T> {
    fn to_std(self) -> Option<T>;
    fn count(&self) -> u8;
}

impl<T, Q> OptionMethods<T> for HasMany<T, Q> {
    fn to_std(self) -> Option<T> {
        Some(self.0)
    }
    fn count(&self) -> u8 {
        2
    }
}

impl<T> OptionMethods<T> for HasSome<T> {
    fn to_std(self) -> Option<T> {
        Some(self.0)
    }
    fn count(&self) -> u8 {
        1
    }
}

impl<T> OptionMethods<T> for HasNothing {
    fn to_std(self) -> Option<T> {
        None
    }
    fn count(&self) -> u8 {
        0
    }
}

// This tests that the dispatch implementation has type annotations
// (i.e. `OptionMethods::<T>::count(inner)`), otherwise the compiler cannot infer the types.
// See issue #26
#[enum_dispatch(OptionMethods<T>)]
enum ManySomeOrNone<T, Q> {
    HasMany(HasMany<T, Q>),
    HasSome(HasSome<T>),
    HasNothing,
}

#[test]
fn test_works() {
    let has_many: ManySomeOrNone<&str, usize> = HasMany("abc", 19usize).into();
    assert_eq!(has_many.count(), 2);
    assert_eq!(has_many.to_std(), Some("abc"));

    let has_some: ManySomeOrNone<&str, usize> = HasSome("abc").into();
    assert_eq!(has_some.count(), 1);
    assert_eq!(has_some.to_std(), Some("abc"));

    let has_nothing: ManySomeOrNone<&str, usize> = HasNothing.into();
    assert_eq!(
        <ManySomeOrNone<&str, usize> as OptionMethods<&'static str>>::count(&has_nothing),
        0
    );
    assert_eq!(
        <ManySomeOrNone<&str, usize> as OptionMethods<&'static str>>::to_std(has_nothing),
        None
    );
}
