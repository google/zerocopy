/// `isValid` defines a structural invariant for a type.
///
/// Under the hood, Anneal will automatically generate a `Anneal.IsValid` instance
/// for this type mapping to the expression below. You can apply it in proofs
/// using `simp_all [Anneal.IsValid.isValid]`.
///
/// ```anneal
/// isValid self := self.val.val > 0
/// ```
pub struct PositiveUsize {
    #[allow(unused)]
    val: usize,
}

/// `isSafe` defines an invariant for an unsafe trait.
///
/// In this trait, we enforce that `Self` has an alignment of exactly 1.
///
/// ```anneal
/// isSafe : ∀ {{_sz : Anneal.core.marker.Sized Self}} {{tl : Anneal.HasStaticLayout Self}},
///   tl.layout.align.val.val = 1
/// ```
pub unsafe trait Unaligned: Sized {}

/// An optimized implementation of addition.
///
/// `unsafe(axiom)` marks this function as an axiom, meaning Aeneas will skip
/// analyzing the body of this function, and Anneal will accept the spec
/// without proof.
///
/// ```anneal, unsafe(axiom)
/// requires: a.val + b.val <= Usize.max
///   -- In Anneal, anonymous `requires` and `ensures` bounds are compiled into
///   -- a struct field named `h_anon`.
/// ensures: ret.val = a.val + b.val
/// ```
#[allow(unused)]
pub unsafe fn fast_add(a: usize, b: usize) -> usize {
    todo!()
}

/// The `requires` block defines a pre-condition named `h_is_safe`.
///
/// Notice the type `Unaligned.Safe T Inst`. When you define an `isSafe` block
/// on a trait, Anneal generates a `.Safe` predicate parameterized by the type `T`
/// and the specific trait implementation `Inst`.
///
/// ```anneal
/// requires (h_is_safe): Unaligned.Safe T Inst
///   -- Defines a post-condition named `h_align_eq`
/// ensures (h_align_eq): ret.val.val = 1
///
///   -- `proof context` is a special block in Anneal. Any `have` bindings
///   -- defined here are made available to ALL subsequent `proof (...)` blocks
///   -- for this function. It prevents duplicating common setup.
/// proof context:
///   -- We can prove the behavior of `fast_add` acting on 0 beforehand.
///   -- Notice how we fulfill the `fast_add.Pre` structure entirely inline
///   -- using `{ ... }` and `simp_all`.
///   --   `Aeneas.Std.Usize`.
///   -- * Note the `#usize` suffixes: Because memory modeling differentiates
///   --   physical sizes (`Usize`) from mathematical sizes (`Nat`), you must
///   --   suffix numerical literals to bypass typeclass resolution ambiguity.
///   have fast_add_zero : ∀ (x : Aeneas.Std.Usize), Anneal.IsValid.isValid x →
///     fast_add x 0#usize = Result.ok x := by
///     intro x h_valid
///     -- Here we supply `{ h_anon := ... }` explicitly for the anonymous `requires` bound!
///     -- Notice `h_a_is_valid`: Anneal injects implicit `h_<arg>_is_valid` preconditions
///     -- for ALL function arguments. We must fulfill them when invoking `.spec`.
///     have ho := fast_add.spec x 0#usize { h_a_is_valid := h_valid, h_anon := by scalar_tac }
///     -- CRACKING MONADIC EXECUTIONS:
///     -- To prove that `fast_add x 0` strictly returns `Result.ok x` and never `fail`/`div`,
///     -- we use `cases ... <;> simp_all`. Because the constraint `ho` requires it to succeed,
///     -- `simp_all` instantly prunes the impossible error states!
///     cases h_eq : fast_add x 0#usize <;> simp_all
///     rename_i r; have _ := ho.h_anon; scalar_tac
///
///   -- Some marker traits (like `Sized`) translates to empty typeclasses.
///   -- We can legally instantiate them with the anonymous constructor `⟨⟩`.
///   have h_sized : Anneal.core.marker.Sized T := ⟨⟩
///
///   -- However, for complex typeclasses like `HasStaticLayout`, Lean's inference
///   -- struggles with fully anonymous instantiations (e.g., `⟨_, _⟩`).
///   -- You must alias complex layouts to a named `have` binding first!
///   --
///   -- IMPORTANT ON TYPECLASS AUTOMATION:
///   -- We are manually defining `HasStaticLayout` here for demonstration scaffolding.
///   -- Standard practice dictates you should NEVER build layout traits manually.
///   -- You should rely on implicit variables (e.g. `[tl : HasStaticLayout T]`)
///   -- provided gracefully by Anneal to your theorems.
///   have h_layout : Anneal.HasStaticLayout T := {
///     layout := {
///       size := 1#usize
///       align := ⟨1#usize, by decide, 0, by rfl⟩
///       sizeAligned := by decide
///     }
///   }
///
///   -- Because `core::mem::align_of` is an external Rust call, Aeneas translates
///   -- it as an opaque axiom. Anneal detects this and injects a `_spec` theorem
///   -- tying it to `HasStaticLayout`. We explicitly pass the typeclass constraints
///   -- using `@` to bypass implicit resolution bugs.
///   have h_aspec : core.mem.align_of T = Result.ok _ :=
///     @core_mem_align_of_spec T h_sized h_layout
///
///   -- TRAIT DICTIONARIES:
///   -- Because of the `T: Unaligned` bound on our function, Aeneas passed us a
///   -- trait dictionary argument named `UnalignedInst`. We feed this dictionary
///   -- to our `h_is_safe` precondition to unlock the theorems stored inside `isSafe`!
///   have h_s := h_is_safe (Inst := UnalignedInst)
///   have h_safe_eq := h_s.isSafe (_sz := h_sized) (tl := h_layout)
///
///   --
///   -- IMPLICIT IDENTIFIERS:
///   -- Notice our use of `ret` and `h_returns`. Where did they come from?
///   -- In Orthogonal WP Proofs, Anneal automatically destructures the `Result`
///   -- of the function into variables like `ret` and `arg'`, and provides the
///   -- `h_returns : get_unaligned_fast_pad ... = ok ret` hypothesis binding them!
///   have h_fast_pad_result : ret.val.val = 1 := by
///     unfold get_unaligned_fast_pad at h_returns
///     -- When unwrapping monadic execution chains (e.g. evaluating `x = Result.ok y`),
///     -- standard rewrites fail. Always apply `rw [..., Aeneas.Std.bind_tc_ok]`!
///     rw [h_aspec, Aeneas.Std.bind_tc_ok] at h_returns
///     have h_valid : Anneal.IsValid.isValid h_layout.layout.align.val := by
///       simp_all [Anneal.IsValid.isValid]
///     rw [fast_add_zero _ h_valid, Aeneas.Std.bind_tc_ok] at h_returns
///     cases ret; simp_all
///
///   -- `h_ret_is_valid` is implicitly demanded by Anneal for all generated structures.
///   -- We can usually dispatch it trivially using `simp_all`.
/// proof (h_ret_is_valid):
///   simp_all [Anneal.IsValid.isValid]
///
///   -- A proof of `h_align_eq`
/// proof (h_align_eq):
///   simp_all
///
///   -- The `h_progress` proof is required when Anneal's `eval_progress` tactic
///   -- fails to automatically discharge the proof.
///   --
///   -- THE PROGRESS BARRIER:
///   -- Why didn't `eval_progress` just work in `h_ret_is_valid`?
///   -- `wp_prove_orthogonal` separates verification into progress and correctness.
///   -- During correctness blocks (`proof (h_ret_...)`), the WP states are destructured.
///   -- The goal state of `h_progress` is an existential equality
///   -- (`⊢ ∃ y, m = ok y`), NOT a Weakest Precondition `spec`. You cannot use
///   -- standard Aeneas `progress` macros to solve it!
/// proof (h_progress):
///   unfold get_unaligned_fast_pad
///
///   -- 1. Scaffolding for core.mem.align_of
///   have h_sized : Anneal.core.marker.Sized T := ⟨⟩
///   have h_layout : Anneal.HasStaticLayout T := {
///     layout := {
///       size := 1#usize
///       align := ⟨1#usize, by decide, 0, by rfl⟩
///       sizeAligned := by decide
///     }
///   }
///   have h_align : ∃ align, core.mem.align_of T = Result.ok align :=
///     ⟨_, @core_mem_align_of_spec T h_sized h_layout⟩
///   rcases h_align with ⟨align, h_align_eq⟩
///
///   -- 2. Scaffolding for fast_add
///   -- We bridge the gap between our generated WP `spec` constraints and the
///   -- existential progress constraint (`∃ y, ...`) using `spec_imp_exists`.
///   have h_add : ∃ padded, fast_add align 0#usize = Result.ok padded := by
///     have ho := fast_add.spec align 0#usize {
///       h_a_is_valid := by simp_all [Anneal.IsValid.isValid]
///       h_b_is_valid := by simp_all [Anneal.IsValid.isValid]
///       h_anon := by scalar_tac
///     }
///     rcases Aeneas.Std.WP.spec_imp_exists ho with ⟨padded, h_eq, _⟩
///     exact ⟨padded, h_eq⟩
///   rcases h_add with ⟨padded, h_add_eq⟩
///
///   -- 3. Conclude progress
///   -- Chain evaluated states seamlessly using `bind_tc_ok`.
///   rw [h_align_eq, Aeneas.Std.bind_tc_ok, h_add_eq, Aeneas.Std.bind_tc_ok]
///   exact ⟨_, rfl⟩
/// ```
pub unsafe fn get_unaligned_fast_pad<T: Unaligned>() -> PositiveUsize {
    let align = core::mem::align_of::<T>();
    let padded = unsafe { fast_add(align, 0) };
    PositiveUsize { val: padded }
}

fn main() {}
