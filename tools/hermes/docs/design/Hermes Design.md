# Hermes: A Literate Verification Toolchain for (`unsafe`) Rust

## 1\. Summary

Hermes is a formal verification orchestrator designed to sit on top of the Aeneas toolchain. Its primary goal is to enable “literate verification” of `unsafe` Rust code: allowing engineers to write formal specifications of function behavior and proofs of correctness (in Lean 4\) directly within Rust source files via standard documentation comments. Where `unsafe` code authors would normally document safety invariants, they write Hermes specifications; where they would normally write safety comments, they write Hermes proofs. Hermes aims to meet developers where they are, asking little of them in the way of new process, while giving them formal assurances about the correctness and security of their code.

## 2\. Background: Charon and Aeneas

To understand Hermes, it is necessary to understand the underlying tools it orchestrates. The base verification pipeline consists of two primary components:

* **Charon:[^1]** A compiler frontend that plugs into `rustc` to extract Rust code (via MIR, Rust’s mid-level intermediate representation) into a simplified, formal intermediate representation known as LLBC (Low-Level Borrow Calculus).  
* **Aeneas:[^2]** A translation tool that takes LLBC and lowers it into pure, functional logic definitions in interactive theorem provers like Lean 4.[^3]

Aeneas achieves ergonomic verification by relying on a crucial simplification: it performs a purely functional translation based on Rust's strict borrow checker rules. It models shared references (`&T`) as pure, immutable values and mutable references (`&mut T`) as state-updating transformations using a "forward/backward" function splitting mechanism.

While this approach is incredibly powerful for Safe Rust, relying on Charon and Aeneas alone presents several significant limitations for verifying real-world systems code:

### 2.1 Inability to Handle Unsafe Operations

Because Aeneas relies on a functional translation rather than a spatial one, it does not model Rust's full memory model (e.g., raw pointers, memory layout, addresses, and aliased mutation). Its abstraction fundamentally assumes that the strict non-aliasing and immutability guarantees of Safe Rust hold, meaning it inherently doesn't capture interior mutation or arbitrary pointer arithmetic. Charon and Aeneas alone are therefore not sufficient to verify the behavior of programs containing unsafe operations.

### 2.2 The Operational Semantics Gap

Formalizing unsafe Rust requires precise reasoning about memory semantics. However, Rust's precise operational semantics are not yet fully specified. Tooling builders are therefore theoretically limited to either guessing what Rust's memory model might eventually be, or waiting until the specification is officially completed—which is realistically many years away.

### 2.3 Ergonomics and Toolchain Friction

Using Aeneas directly requires developers to adopt an entirely new toolchain (Lean), author manual verification definitions at-a-distance from their source Rust code, and ensure that they remain up-to-date as the Rust code changes. These ergonomic speedbumps significantly increase the barrier to entry for practical verification.

## 3\. Hermes' Core Contributions

Hermes is designed to orchestrate Charon and Aeneas while systematically resolving the limitations outlined above.

### 3.1 Axiomatizing Leaf Functions

Much real-world unsafe code does not directly invoke the specific unsafe “leaf” operations that Aeneas cannot support (such as raw pointer dereferences). Instead, it either indirectly invokes these operations via function indirection, or it creates values that will later flow into leaf operations during subsequent method calls (for example, manipulating the length field in `Vec::set_len`).

Since Aeneas successfully translates all of these intermediate operations and standard Rust control flow, it still gets us most of the way toward being able to verify the behavior of programs containing unsafe code. Hermes closes this remaining gap by providing an ergonomic syntax for users to axiomatize the behavior of their specific "leaf" functions—the ones that perform the unsafe leaf operations that Aeneas cannot model. This allows the broader program's composition to be verified using Aeneas's functional translation.

*Note that many leaf operations are supported behind standard library APIs (e.g. `std::ptr::read`). This allows Hermes to ship with its own axiomatizations of these APIs. Our hope is that, in practice, it will be rare that Hermes users need to axiomatize their own functions.*

### 3.2 Lower-Bound Memory Axioms

Hermes avoids needing to wait for Rust's operational semantics to be fully specified by instead encoding a set of lower-bound memory axioms. These axioms represent fundamental properties (such as size and alignment constraints) that are guaranteed by the Rust Reference, and are thus guaranteed to hold in *any* future memory model.[^4] This approach allows users to prove the soundness of unsafe code without requiring the toolchain to guess the exact future shape of Rust's abstract machine.

### 3.3 Meeting Rust Programmers Where They Are

Hermes abstracts away the need to manually author Lean specifications in separate files. It meets Rust programmers where they are by adopting the existing syntax of safety doc comments (i.e., a description of an API's safety invariants written in a doc comment). While proofs are currently authored in doc comments, a slight departure from the existing practice of writing safety comments inline (e.g. inside of a function’s body), Hermes plans to add support for inline safety comments. This literate programming approach keeps code, formal specifications, and proofs tightly synchronized.

## 4\. Architecture

Once a programmer has annotated their Rust code with Hermes annotations (whose syntax is described in Section 5), interacting with Hermes is just a matter of running `cargo hermes verify`. Like the familiar `cargo check`, `cargo hermes verify` will exit cleanly on successful verification, or will print error messages describing verification failures.

Hermes primarily operates by orchestrating the Charon, Aeneas, and Lean verification tools, managing the flow between Rust source, LLBC, and Lean through distinct stages:

* **Literate Extraction & Analysis**  
  Hermes begins by parsing the Rust source text to extract Hermes specifications, models, and proofs directly from standard doc comments (`///`).  
* **Charon/Aeneas Toolchain**  
  * **Lowering to LLBC**  
    Charon is used to lower the source Rust to LLBC. Charon’s `--start-with` is used to specify the list of Rust functions which carry Hermes annotations, instructing Charon to only lower code which is reachable from these functions. Besides the obvious performance benefits, this ensures that Hermes can support any project so long as all *reachable* code is supported by Charon/Aeneas. Constructs which are *not* reachable from Hermes-annotated functions do not need to be supported.  
  * **Lowering to Lean**  
    Aeneas is used to lower the resulting LLBC to Lean.  
* **Hermes Toolchain**  
  In parallel, Hermes generates Lean directly from the user’s Hermes annotations:  
  * **Specs & Proofs**  
    Users may annotate Rust functions with Lean specifications of their behavior using a `spec` block. When they do this, they are required to include an accompanying `proof` block proving that their implementation (specifically, the Lean generated by Aeneas) satisfies the specification.  
  * **Leaf Modeling**  
    To handle Aeneas’s limitations with unsafe code, Hermes permits the user to mark a function using an `unsafe(axiom)` block, which includes a Lean specification just like a `spec` block. Unlike `spec`, however, an `unsafe(axiom)` block instructs Hermes to treat the function as opaque and accept the specification as axiomatic. Hermes flags the function as `--opaque` to Charon, and generates a Lean `axiom` derived from the user’s `unsafe(axiom)`. By making this axiom available in Lean, Hermes is able to verify the safe composition of the surrounding program while treating the unsafe leaf as a trusted black box.  
  * **Type and Trait Invariants**  
    To improve ergonomics, Hermes has built-in support for declaring type and `unsafe trait` invariants. These are explored in more detail below. As with other Hermes concepts, type and trait invariants are declared in Lean using Hermes annotations, and compiled against the Lean generated by Aeneas.  
* **Verification & Transparent Feedback**  
  Finally, Hermes invokes the Lean compiler. To preserve the literate programming experience, Lean compilation errors are captured and transparently line-mapped back to the exact doc comment in the Rust source file. The developer never needs to leave their Rust editor to understand why a proof failed.

## 5\. Syntax Specification

Hermes uses standard Rust documentation comments with a specific info string to identify Hermes annotations.

Where possible, Hermes syntax omits introducing variable bindings, keeping these implicit, as they are usually obvious and match the Rust surface syntax. For example, when defining the specification of `wrapper` in 5.1 below, the Lean signature `wrapper (a: U32) -> U32` is omitted.

### 5.1 The `spec` and `proof` Blocks (Safe Verification)

Used to specify the behavior of standard Rust functions that Aeneas can translate, and prove that specification correct.

**Syntax:**

````rust
/// ```lean, hermes, spec
/// ensures: ret.val = a.val
/// proof:
///   rw [wrapper]
///   obtain ⟨ret_val, h_eq⟩ := safe_div_spec a 1#u32 (by decide)
///   simp_all [Nat.div_one]
///   omega
/// ```
pub fn wrapper(a: u32) -> u32 {
    unsafe { safe_div(a, 1) }
}
````

*Since specs are the common case, the `spec` token is optional – a `hermes` info string on a function is equivalent to `hermes, spec`.*

**Semantics:**

* Hermes allows Aeneas to generate Lean for this function  
* Hermes generates Lean for the specification and proof, allowing Lean to verify that the proof is correct (i.e., that the specification faithfully describes the function’s behavior)

**Generated Lean:**

```lean4
-- Generated by Aeneas:
def wrapper (a : Std.U32) : Result Std.U32 := do
  safe_div a 1#u32

-- Generated by Hermes:
namespace wrapper

  structure Pre (a : Std.U32)  : Prop where
    h_a_is_valid : Hermes.IsValid.isValid a := by verify_is_valid h_a_is_valid

  structure Post (a : Std.U32)  (ret : Std.U32) : Prop where
    h_ret_is_valid : Hermes.IsValid.isValid ret := by verify_is_valid h_ret_is_valid
    h_unnamed : ret.val = a.val := by verify_user_bound h_unnamed

theorem spec (a : Std.U32)
  (h_req : Pre a) :
  Aeneas.Std.WP.spec (wrapper a) (fun ret_ => Post a ret_) := by ...

end wrapper
```

### 5.2 The `unsafe(axiom)` Block (Unsafe/Opaque)

Used for functions containing unsafe code that Aeneas cannot translate – i.e., those which perform “leaf” unsafe operations. Just as with normal `unsafe` Rust code, Hermes treats `unsafe(axiom)` annotations as given, and does not attempt to verify their correctness. **Buggy `unsafe(axiom)` annotations can lead to unsound programs.**

Note that many leaf operations are supported behind standard library APIs (e.g. `std::ptr::read`). This allows Hermes to ship with its own axiomatizations of these APIs. Our hope is that, in practice, it will be rare that Hermes users need to axiomatize their own functions.

**Example:**

````rust
/// ```lean, hermes, unsafe(axiom)
/// requires (h_non_zero): b.val > 0
/// ensures (h_result): ret.val = a.val / b.val
/// ```
pub unsafe fn safe_div(a: u32, b: u32) -&gt; u32 {
    unsafe { a / b }
}
````

*The `unsafe(...)` syntax is used to call the developer’s attention to the fact that they’re doing something risky, and is chosen to mirror Rust’s syntax for unsafe attributes like `#[unsafe(no_mangle)]`.*

*Hermes also supports named predicates, which are used to disambiguate when multiple `requires` or `ensures` are present.*

**Semantics:**

* Hermes passes `--opaque` to Charon for this function, instructing it not to generate LLBC for the function’s body; Aeneas similarly omits the body in the lowered Lean  
* Hermes uses the user’s `axiom` to generate a Lean `axiom` about the behavior of this function

**Generated Lean:**

```lean4
-- Generated by Aeneas:
opaque safe_div (a : Std.U32) (b : Std.U32) : Result Std.U32

-- Generated by Hermes:
namespace safe_div

  -- The Pre structure encapsulates all preconditions
  structure Pre (a b : Std.U32) : Prop where
    h_non_zero : b.val > 0

  -- The Post structure encapsulates all postconditions
  structure Post (a b ret : Std.U32) : Prop where
    h_result : ret.val = a.val / b.val
  
  axiom spec (a : Std.U32) (b : Std.U32) (h_req : safe_div.Pre a b) :
    Hermes.SpecificationHolds
      (α := Std.U32)
      (safe_div a b)
      (fun ret =&gt; safe_div.Post a b ret)

end safe_div
```

### 5.3 Type Invariants

Used to specify that a type has internal field invariants.

**Syntax:**

````rust
/// ```lean, hermes/// isValid self := 2 | self.x.val/// ```pub struct Even {    x: usize,}
````

**Semantics:**

* The Hermes standard library includes an `IsValid` type class; this annotation instructs Hermes to implement `IsValid` for `Even` using the provided `isValid` implementation  
* Adds `(h_valid: IsValid.isValid arg)` arguments to specs for any function taking this type as an input  
* Adds `/\ IsValid.isValid ret` to `ensures` clauses for any function returning this type

**Generated Lean:**

```lean4
-- Generated by Aeneas:
structure Even where
  x : Std.Usize

-- Generated by Hermes:
namespace Even

instance : Hermes.IsValid Even where
  isValid self := 2 | self.x.val

end Even
```

### 5.4 Trait Invariants

Used to specify that an unsafe trait denotes that a type satisfies an invariant.

**Syntax:**

````rust
/// ```lean, hermes/// isSafe : .../// ```pub unsafe trait FromBytes {}
````

**Semantics:**

* Requirement (Implementation Site): When a user writes `unsafe impl FromBytes for MyType`, Hermes requires them to prove that `isSafe(MyType)` holds.  
* Guarantee (Call Site): When a generic function has a bound `<T: FromBytes>`, the Hermes-generated spec automatically includes a hypothesis `(hSafe: isSafe T)`, allowing the proof to rely on that property.

**Generated Lean:**

```lean4
-- Generated by Aeneas:
structure FromBytes (Self : Type) where

-- Generated by Hermes:
namespace FromBytes

class Safe (Self : Type) [FromBytes Self] : Prop where
  isSafe : ...

end FromBytes
```

## 6\. Desugaring to Aeneas

To understand how Hermes’ surface syntax works, we must understand how Aeneas handles references. Aeneas achieves its verification ergonomics by performing a purely functional translation based on Rust’s strict borrow checker rules. It completely abstracts away raw memory, pointers, and spatial reasoning.

Hermes allows developers to write specifications that look like standard, stateful Rust, and desugars them into theorems that apply to Aeneas’s generated pure functions.

### 6.1 Immutable References (`&T`)

Because the Rust compiler guarantees that immutable references cannot be modified while they are borrowed (for types without interior mutability), Aeneas models shared references (`&T`) as pure, immutable values. There is no memory to dereference; a `&u32` in Rust simply lowers to a `U32` value in Lean.

This is the simple case – there is a clear, intuitive, one-to-one mapping from surface Rust source code to generated Lean code. This allows Hermes to support a surface syntax for Hermes annotations that is passed through mostly unmodified to Lean.

**Rust source:**

````rust
/// ```lean, hermes, spec
/// ensures: ret.val = x.val
/// proof:
///   ...
/// ```
pub fn read_val(x: &u32) -> u32 {
    *x
}
````

**Generated Lean:**

Aeneas generates a single function, and Hermes generates a straightforward theorem tying the input to the result:

```lean4
-- Generated by Aeneas:
def read_val (x : Std.U32) : Result Std.U32 := do
  ok x

-- Generated by Hermes:
namespace read_val

  structure Pre (x : Std.U32)  : Prop where
    h_x_is_valid : Hermes.IsValid.isValid x := by verify_is_valid h_x_is_valid

  structure Post (x : Std.U32)  (ret : Std.U32) : Prop where
    h_ret_is_valid : Hermes.IsValid.isValid ret := by verify_is_valid h_ret_is_valid
    h_unnamed : ret.val = x.val := by verify_user_bound h_unnamed

theorem spec (x : Std.U32)
  (h_req : Pre x) :
  Aeneas.Std.WP.spec (read_val x) (fun ret_ => Post x ret_) := by ...

end read_val
```

### 

### 6.2 Mutable References (`&mut T`)

Mutable references require more complex handling. Aeneas models mutable references (`&mut T`) as state-updating transformations by having the lowered function return a tuple containing both the standard return value and the updated state of the mutably borrowed values

To prevent the developer from having to manually destructure this tuple in their specifications, Hermes unifies everything into a single `spec` block using the `x`/`x'` syntax and the implicit `ret` keyword.

* `ret` implicitly binds to the successful (i.e., non-panicking) result of the forward function.  
* If `x: &mut _`, then in the Hermes annotation, `x` refers to the state of the mutably referenced value *before* the function executes (this is the input to the Lean function).  
* `x'` refers to the state of the variable *after* the function executes (this is the “new state” output of the Lean function).

**Rust Source:**

````rust
/// ```lean, hermes, spec
/// ensures: x'.val = x.val + add.val
/// proof:
///   ...
/// ```
pub fn add_in_place(x: &mut u32, add: u32) {
   *x += add;
}
````

**Generated Lean:**

Hermes automatically matches the return type generated by Aeneas, generating local let-bindings that destructure the result tuple into the return value and the post-state variables (like `x'`).

```lean4
-- Generated by Aeneas:
def add_in_place (x : Std.U32) (add : Std.U32) : Result Std.U32 := do
  x + add

-- Generated by Hermes:
namespace add_in_place

  structure Pre (x : Std.U32) (add : Std.U32)  : Prop where
    h_x_is_valid : Hermes.IsValid.isValid x := by verify_is_valid h_x_is_valid
    h_add_is_valid : Hermes.IsValid.isValid add := by verify_is_valid h_add_is_valid

  structure Post (x : Std.U32) (add : Std.U32)  (x' : Std.U32) : Prop where
    h_x'_is_valid : Hermes.IsValid.isValid x' := by verify_is_valid h_x'_is_valid
    h_unnamed : x'.val = x.val + add.val := by verify_user_bound h_unnamed

theorem spec (x : Std.U32) (add : Std.U32)
  (h_req : Pre x add) :
  Aeneas.Std.WP.spec (add_in_place x add) (fun ret_ =>
    let x' := ret_
    Post x add x') := by ...

end add_in_place
```

### 6.3 Complex Combinations

When a function both mutates state *and* returns a meaningful value, Hermes automatically destructures the tuple to bind the correct components to `ret`  and the updated variables (e.g. `stack'`).

**Rust Source:**

````rust
/// ```lean, hermes
/// requires (h_req): stack.len > 0
/// ensures (h_len): stack'.len = stack.len - 1
/// ensures (h_ret): ret = stack[stack.len - 1]
/// proof:
///   ...
/// ```
pub unsafe fn pop(stack: &mut Vec<u32>) -> u32 {
   stack.pop().unwrap()
}
````

**Generated Lean:**

```lean4
-- Generated by Aeneas:
def pop
  (stack : alloc.vec.Vec Std.U32) :
  Result (Std.U32 × (alloc.vec.Vec Std.U32))
  := do
  let (o, stack1) ← alloc.vec.Vec.pop Global stack
  let i ← core.option.Option.unwrap o
  ok (i, stack1)

-- Generated by Hermes:
namespace pop

  structure Pre (stack : (Vec Std.U32))  : Prop where
    h_stack_is_valid : Hermes.IsValid.isValid stack := by verify_is_valid h_stack_is_valid
    h_req : stack.len > 0

  structure Post (stack : (Vec Std.U32))  (ret : Std.U32) (stack' : (Vec Std.U32)) : Prop where
    h_ret_is_valid : Hermes.IsValid.isValid ret := by verify_is_valid h_ret_is_valid
    h_stack'_is_valid : Hermes.IsValid.isValid stack' := by verify_is_valid h_stack'_is_valid
    h_len : stack'.len = stack.len - 1 := by verify_user_bound h_len
    h_ret : ret = stack[stack.len - 1] := by verify_user_bound h_ret

theorem spec (stack : (Vec Std.U32))
  (h_req : Pre stack) :
  Aeneas.Std.WP.spec (pop stack) (fun ret_ =>
    let (ret, stack') := ret_
    Post stack ret stack') := by ...

end pop
```

By handling this desugaring under the hood, Hermes ensures the proof engineer only has to reason about a single, unified local context that maps directly to the original Rust source.

## 7\. Theoretical Foundation: Memory Modeling

Rust's operational semantics are not yet fully formally specified. However, the Rust Reference and standard library make certain "lower bound" guarantees regarding memory layout and behavior. Hermes utilizes these guarantees to justify authoring Lean axioms about Rust's memory model, particularly for `unsafe` code.

### 7.1 Lower Bound Guarantees

While a precise memory model is absent, Hermes assumes that any future formalization of Rust will satisfy key properties guaranteed by the current Rust [Reference](https://doc.rust-lang.org/stable/reference/) and [standard library documentation](https://doc.rust-lang.org/stable/std/). For example, Rust guarantees [the following](https://doc.rust-lang.org/1.92.0/reference/type-layout.html#size-and-alignment) about sized types:

* **Alignment:** Sized types have an alignment, which is always a non-zero power of two.  
* **Size:** The size of a type is always a multiple of its alignment.

To see how this is useful, consider the following Rust type:

```rust
struct Foo {
    a: u32,
    b: u8,
}
```

Rust [guarantees](https://doc.rust-lang.org/1.92.0/reference/type-layout.html#the-rust-representation) that the `a` and `b` fields are properly aligned, don’t overlap, and that the alignment of `Foo` is at least as large as the alignments of `a` and `b`. Other than that, it makes no guarantees about the layout of `Foo`. Regardless, we can still infer useful properties about this type: For example, we can infer that `size_of::<Foo>() >= size_of::<u32>() + size_of::<u8>()`, that `size_of::<Foo>() % align_of::<u32>() == 0`, etc.

### 7.2 The Memory Axioms

Hermes encapsulates these guarantees into a set of Lean definitions, type classes, and axioms included in its standard library. This allows users to prove the soundness of `unsafe` code – such as raw pointer manipulation or manual memory layout calculation – without requiring Aeneas to model the entire Rust abstract machine.

For example, this model of type layout is included in the Hermes standard library:

```lean4
class Layout (ɑ : Type) where
  size : Nat
  align : Nat
  validAlignment : Alignment align
  sizeAligned : size | align
```

## 8\. Tooling

Hermes wraps the underlying tools (Charon, Aeneas, and Lean) to provide a seamless “Cargo-like” experience.

### 8.1 CLI Interface

Hermes accepts standard Cargo flags to identify packages and targets. It also accepts an `--allow-sorry` flag, useful for incremental development, that allows incomplete or missing proofs to verify (in reference to Lean’s `sorry` proof step, which is also used for this purpose).

```
$ cargo hermes verify --helpVerify a crateUsage: cargo hermes verify [OPTIONS]Options:      --allow-sorry            Allow `sorry` in proofs and inject `sorry` for missing proofs      --manifest-path <PATH>   Path to Cargo.toml  -p, --package <SPEC>         Package to process      --workspace              Process all packages in the workspace      ... (standard cargo targeting flags) ...
```

## 9\. Limitations & Future Work

### 9.1 Known Limitations

* **Complex Lifetimes:** Functions that return mutable borrows derived from inputs (e.g., `fn choose<'a> (x: &'a mut i32, y: &'a mut i32) -> &'a mut i32)` have highly complex backward functions in Aeneas involving "future" return values.  
* **Interior Mutability: **Code using interior mutation (such as `RefCell` or `Mutex`) must be marked `opaque` and manually modeled, as Aeneas does not support interior mutation.

### 9.2 Open Questions

* **Symbolic Address Modeling: **How to expose the "address" of a reference in Lean without breaking the clean value semantics, specifically regarding type indistinguishability between `T` , `&T` , and `&&T`. Because Aeneas’ functional translation recursively unwraps references to expose their values for functional reasoning, the specific layer of indirection—and thus the identity of the memory location holding the value—is obscured in the generated type system.  
* **Interior Mutability: **Finding a way to extend functional translation to support limited forms of interior mutability (e.g., `Cell`) without a full global heap model.  
* **Recursive Reference Containment:** A related challenge to symbolic address modeling is handling types that recursively contain references. In Rust, a `struct S<'a>` can contain a `&'a T` . In the functional translation, `S` might be lowered to a type containing `T` directly (value semantics). When verifying memory layout or unsafe casts, the physical representation of `S` (containing a pointer) differs from its logical representation (containing a value). If `T` itself contains further references, the divergence between the physical layout (a tree of pointers) and the logical model (a tree of values) grows. Reconciling these views to prove that a specific offset in `S` corresponds to a valid memory address for a sub-field requires a robust mapping between the "Logical Value" and the "Physical Backing Store," which is currently not fully defined.

### 9.3 Future Work

* **Interactive IDE Support:** Enabling interactive theorem proving directly within the Rust IDE (e.g., VS Code). A Hermes IDE extension would spin up a Lean server in the background and synchronize the cursor position within Rust doc comments (proof blocks) to the generated Lean files. This would allow users to see the goal state and receive tactic suggestions in real-time, bringing the full power of Lean's interactive editing to the Rust environment.  
* **Separation Logic Support:** Implementing a Separation Logic framework within Lean to allow natural reasoning about heap states inside spec/proof/axiom blocks.  
* **Specifications in Rust:** Since Charon/Aeneas support translating Rust to Lean, we could support writing Hermes specifications in *Rust* and use Charon/Aeneas to translate these to Lean, thus effectively allowing programmers to write their specifications in native Rust instead of Lean.  
* **Type System Extensions:** Treating Hermes annotations as de-facto extensions to the Rust type system (refinement types).  
* **Mandatory Unsafe Documentation:** A "strict mode" that fails verification if any unsafe block lacks a Hermes annotation.  
* **User-authored proofs:** We may want to eventually permit users to write more complex Lean code that is checked into source control in stand-alone `.lean` files. Hermes should support including these in the build.  
* **Axiom \+ Lean body:** It may be useful to allow users to provide a Lean model for an axiomatized function and provide a proof that the Lean model satisfies their axiom. While this doesn’t guarantee that their axiom reflects the behavior of the Rust function, it may nonetheless be useful to help catch mistakes in model definition.

## 10\. Appendix A: Syntax Specification

Hermes specifications are written within standard Rust documentation comments (`///`) using a fenced code block annotated with `hermes` (note that preceding annotations are ignored, as in `lean, hermes` – this allows support for annotations used for other purposes such as syntax highlighting).

To reliably extract these specifications without requiring a full Lean 4 parser inside the Rust toolchain, Hermes employs a **line-oriented, indentation-sensitive** grammar.

### 10.1 Grammar Rules

The parser reads the specification block line by line as a state machine. The content is divided into clauses based on recognized keywords.

1. **Keywords:** The keywords `context`, `requires`, `ensures`, `proof`, `axiom`, `isValid`, and `isSafe` trigger a transition to a new section. To be recognized, a keyword must be the first non-whitespace text on a line. Inline arguments are permitted (e.g., `requires x > 0`).  
   1. Note: `isValid` and `isSafe` are treated as keywords for uniform parsing, although to the user they appear to be function names (e.g. `isValid self := ...`), and Hermes generates Lean functions of the same names.  
2. **The Off-side Rule (Continuations):** When a keyword is encountered, its exact indentation level (the number of leading spaces) becomes the **baseline**. Any subsequent line that belongs to this clause *must* be indented strictly more than the baseline.   
3. **Blank Lines:** Lines containing only whitespace are ignored for the purpose of indentation checking.

### 10.2 Examples

**Valid syntax:**

````rust
/// ```lean, hermes, spec
/// context:                   -- New section (Baseline: 0 spaces)
///   open Aeneas              -- Valid continuation (2 > 0)
///   let limit := 100         -- Valid continuation (2 > 0)       
///
/// requires:                  -- New section (Baseline: 0 spaces)
///   x < limit                -- Valid continuation (2 > 0)
///   && x > 0                 -- Valid continuation (2 > 0)
/// 
/// ensures: ret = x + 1       -- New section (Baseline: 0 spaces)
///
/// proof:                     -- New section (Baseline: 0 spaces)
///   intros                   -- Valid continuation (2 > 0)
///   simp [limit] at *        -- Valid continuation (2 > 0)
/// ```
````

#### **Invalid syntax:**

````rust
/// ```lean, hermes, spec
/// requires:
///   a > 0
/// ensure:        -- ERROR: Invalid indentation / Unknown keyword
///   b > 0
/// ```
````

### 10.3 Motivation

This design was chosen over both unstructured text parsing and fully structured AST parsing for three key reasons:

1. **The “typo'd keyword” trap:** If a user makes a typo (like writing `ensure` instead of `ensures` in the invalid example above), a naive parser would fail to recognize the new section. Without the Off-side Rule, `ensure \n b > 0` would be silently appended to the `requires` clause. Hermes would report success, but Lean would later fail with a cryptic error (`unknown identifier 'ensure'`) pointing to the middle of an expanded theorem body. By enforcing indentation boundaries, Hermes immediately detects the structural violation in Rust and emits a precise, localized diagnostic: *"Invalid indentation: expected an indented continuation or a valid Hermes keyword. Did you misspell a keyword?"*  
2. **Treating Lean as a black box:** Writing a complete, robust Lean 4 parser in Rust is a monumental and fragile task. By relying strictly on leading keywords and indentation levels, Hermes can safely route multi-line blocks of complex Lean syntax (including macros, custom notations, and comments) to the correct location in the generated `.lean` file without ever needing to understand the syntax itself.  
3. **Ergonomic alignment:** Lean 4 is already a whitespace-sensitive language. Requiring users to use indentation to demarcate scope—where Hermes directives sit at an outer scope and Lean expressions sit at an inner scope—feels completely natural and enforces highly readable documentation.

## 11\. Appendix B: Under the Hood

### 11.1 Target Directory Layout

Hermes isolates its build artifacts to avoid conflicting with standard Cargo builds or other Hermes instances. It places its artifacts in \`target\` (or wherever the user has configured their Cargo target directory), specifically in `target/hermes/<hash>`, where `<hash>` is a hash of the absolute path to the workspace root to ensure freedom from conflicts.

```
target/hermes/<hash>/
    llbc/                   # LLBC files (produced by Charon)
    lean/                   # Lean files (produced by Hermes and Aeneas)
        lakefile.lean
        lean-toolchain
        hermes/             # The Hermes Standard Library
            Prelude.lean
            ...
        generated/          # Generated by Aeneas and Hermes
            <crate_name>/
                Funs.lean
                ...
        user/               # (Future extension) User-authored proofs

```

### 

### 11.2 Lakefile

Hermes generates a \`lakefile.lean\` to configure the build. If `--allow-sorry` is passed, Hermes relaxes compiler settings (removing `-DwarningAsError=true`).

```lean4
import Lake
open Lake DSL

require aeneas from git
  "https://github.com/AeneasVerif/aeneas" @ "main" / "backends/lean"

package hermes_verification

-- The library generated by Aeneas
lean_lib «Generated» where
  srcDir := "generated"

-- The Hermes standard library and extracted models
lean_lib «Hermes» where
  srcDir := "hermes"

-- The user's proofs extracted from comments
lean_lib «User» where
  srcDir := "user"
```

[^1]:  [https://github.com/AeneasVerif/charon](https://github.com/AeneasVerif/charon)

[^2]:  [https://github.com/aeneasVerif/aeneas](https://github.com/aeneasVerif/aeneas)

[^3]:  Aeneas also supports lowering to F\*, Coq, and HOL4.

[^4]:  We can think of Rust’s current normative reference documents – the [Reference](https://doc.rust-lang.org/reference/introduction.html) and [standard library documentation](https://doc.rust-lang.org/stable/std/) – as defining an informal axiomatic semantics for Rust. While an operational semantics defines a step function between precisely-defined program states, an axiomatic semantics defines a (possibly multi-) step function between *sets* of program states (specifically, each is the set of program states which satisfy a particular logical predicate). Since Rust’s current normative documentation under-specifies this step function, it effectively defines an axiomatic semantics which will *approach* a full operational semantics over time as more axioms are added.