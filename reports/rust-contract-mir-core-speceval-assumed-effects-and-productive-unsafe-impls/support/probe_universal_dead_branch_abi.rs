#![allow(unused)]

pub mod anneal_abi {
    #[inline(never)]
    pub fn contract_requires<F: FnOnce() -> bool>(_f: F) {}

    #[inline(never)]
    pub fn contract_old<T, F: FnOnce() -> T>(_f: F) -> T {
        loop {}
    }

    #[inline(never)]
    pub fn contract_ensures<Ret: ?Sized, F: FnOnce(&Ret) -> bool>(_f: F) {}

    #[inline(never)]
    pub fn contract_unwinds_if<F: FnOnce() -> bool>(_f: F) {}
}

pub fn bump_mut(x: &mut u32) -> u32 {
    if false {
        anneal_abi::contract_requires(|| *x < u32::MAX);
        let __old_0 = anneal_abi::contract_old(|| *x);
        anneal_abi::contract_ensures::<u32, _>(|ret| *x == __old_0 + 1 && *ret == __old_0);
    }
    let prev = *x;
    *x = prev + 1;
    prev
}

pub fn consume_non_copy(v: Vec<u8>) -> usize {
    if false {
        anneal_abi::contract_requires(|| !v.is_empty());
        let __old_0 = anneal_abi::contract_old(|| v.len());
        anneal_abi::contract_ensures::<usize, _>(|ret| *ret == __old_0);
    }
    let n = v.len();
    drop(v);
    n
}

pub fn lifetime_ref<'a>(s: &'a [u8]) -> &'a u8 {
    if false {
        anneal_abi::contract_requires(|| !s.is_empty());
        let __old_0 = anneal_abi::contract_old(|| s[0]);
        anneal_abi::contract_ensures::<&'a u8, _>(|ret| **ret == __old_0);
    }
    &s[0]
}

pub fn generic_swap<T: Copy + PartialEq>(x: &mut T, y: T) -> T {
    if false {
        let __old_x = anneal_abi::contract_old(|| *x);
        anneal_abi::contract_ensures::<T, _>(|ret| *ret == __old_x && *x == y);
    }
    let old = *x;
    *x = y;
    old
}

pub fn mut_ref_early_ret(x: &mut u32) -> Result<u32, u32> {
    if false {
        anneal_abi::contract_requires(|| *x < 100);
        let __old_0 = anneal_abi::contract_old(|| *x);
        anneal_abi::contract_ensures::<Result<u32, u32>, _>(|ret| match ret {
            Ok(v) => *x == __old_0 + 1 && *v == *x,
            Err(e) => *x == __old_0 && *e == 0,
        });
        anneal_abi::contract_unwinds_if(|| *x == __old_0);
    }
    if *x == 0 {
        return Err(0);
    }
    *x += 1;
    Ok(*x)
}

// Test: what if a parameter is `mut` by value AND mutated in body?
pub fn mut_val_param(mut x: u32) -> u32 {
    if false {
        anneal_abi::contract_requires(|| x < 100);
        let __old_0 = anneal_abi::contract_old(|| x);
        anneal_abi::contract_ensures::<u32, _>(|ret| *ret == __old_0 + 1);
    }
    x += 1;
    x
}
