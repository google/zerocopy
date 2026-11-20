# Landin's Knot, Stored Closures, Cantor Barriers, and Fuel-Indexed Defunctionalization in Lean 4 Separation Logic

## Summary

Unindexed first-order affine separation logic in Lean 4's monomorphic base universe (`Type 0`, modeled via upward-closed predicates `IProp` over disjoint partial maps `Frag := Nat → Option Resource`) verifies almost all systems-level Rust idioms natively—including raw pointers, `Cell<T>`, `RefCell<T>`, `OnceCell<T>`, cyclic `Rc<RefCell<Node>>` pointer graphs, and stack-scoped closures (`F: FnMut(T) -> U`). Cyclic heap pointers do **not** require step-indexing (`later`, `▷`), because graph invariants map finite allocation identifiers (`AllocId`) to concrete first-order node values rather than storing heap predicates inside `Resource`.

The strict boundary sits at **impredicative higher-order store**, exemplified by Landin's knot (`Rc<RefCell<Option<Box<dyn Fn(u32) -> u32>>>>`), reentrant `Arc<Mutex<Vec<Box<dyn FnOnce() + Send>>>>` task queues, and mutably swappable `RawWakerVTable` dispatch tables. Attempting to store `IProp` inside `Resource` triggers two independent obstructions: (1) Lean 4's kernel inductive checker (`src/kernel/inductive.cpp`) rejects non-positive occurrences of `Resource` in `(Nat → Option Resource) → Prop` (and rejects `Type 1` witness structures such as `Σ α : Type 0, ...` inside `Type 0` constructors), and (2) **Cantor's diagonal theorem** holds constructively even when restricted to upward-closed separation-logic predicates ($2^{|\text{Resource}|}$ distinct singleton-key predicates $U_D$ cannot inject into `Resource`).

Full higher-order concurrent separation logic (`Iris`, mechanized in Lean 4 by `leanprover-community/iris-lean`) solves this circularity through ordered families of equivalences (`OFE`), inverse-limit `Tower` fixpoints (`COFESolver`), universe-polymorphic `Type u` definitions, and the contractive `▷` modality. For minimal `Type 0` Lean 4 verification engines without COFEs or universe polymorphism, two `Type 0` encodings recover soundness for stored closures under partial correctness: **(a) closed-crate defunctionalization** (`InvCode := DefId × Val`) and **(b) fuel-indexed predicates** (`StepIProp := Nat → IProp`), where `stepLater` synchronizes 1-for-1 with the structural `fuel : Nat` decrement of big-step/small-step weakest preconditions to discharge `@Nat.rec` Löb induction and detect runtime `RefCell` borrow-panic traps (`BorrowMutError`) without COFEs.

## Applicability

These findings govern separation-logic verification in **Lean 4** (`leanprover/lean4` `44db45ca210151a9fc25f10b8d7fa4535856680f` and `leanprover-community/iris-lean` `5540ef0110fc8f6d8e495c10c2f238c3ede14f3b`) targeting **Rust** interior mutability, reference-counted cycles, and stored trait-object closures (`rust-lang/rust` `ec65cd52bba13d491ff65c9d218b39753755c84a`).

The report compares three formal architectures:
1. **Unindexed first-order affine separation logic (`Type 0`)**: grounded in `JoJoDeveloping/tiny-iris` (`5b18c311e746d2ae4170b0d253b5d7d36ee5d6d9`), `AeneasVerif/aeneas` (`2e3d4488280bb8a95411db81019a7854a784861f`; Ho & Protzenko, ICFP 2022), and constructive `Frag → Prop` upward-closed predicates.
2. **Higher-order step-indexed separation logic (`Iris`)**: grounded in Jung et al. (JFP 2018) and `leanprover-community/iris-lean` (`5540ef0110fc8f6d8e495c10c2f238c3ede14f3b`; de Medeiros et al., 2026).
3. **Closed-world `Type 0` defunctionalization and finite-fuel `StepIProp`**: derived from Reynolds (1972) and fuel-clocked operational semantics (Owens et al., ESOP 2016), validated against Rust's `RefCell`, `Rc`, and `Fn` implementations (`ec65cd52bba13d491ff65c9d218b39753755c84a`).

Related corpus packages cover adjacent areas without duplicating this boundary analysis: `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic` covers transfinite liveness; `fuel-step-indexing-clocks-and-tcb-recursion` examines operational step clocks; `aeneas-types-traits-closures-and-external-models` covers static trait/closure translation; `ghostcell-branded-tokens-intrusive-containers-and-generational-arenas` covers linear branded cells; and `lean-separation-logics-iris-and-virtual-isa-verification` covers virtual-ISA separation logics. Findings assume sequential or coarse-lock-synchronized execution; weak-memory atomic closure publication and total-correctness liveness over non-terminating higher-order loops fall outside the finite-fuel adequacy theorem.

## Findings

### 1. First-Order `Type 0` Affine Separation Logic (`Frag`, `IProp`, and Frame-Quantified Adequacy)

Basis: source + derived

In an unindexed first-order affine separation logic inside Lean 4 (`Type 0`), heap assertions are upward-closed predicates over finite-domain partial resource maps:

```lean
namespace UnindexedSL

inductive Resource where
  | cellSlot   (alloc off : Nat) (bytes : List UInt8)
  | refCellTok (alloc : Nat) (flag : Int) (payloadOwned : Bool)
  | rcHeader   (alloc strongCount weakCount : Nat) (dropping : Bool)

def resourceCompat (r1 r2 : Resource) : Bool :=
  match r1, r2 with
  | .cellSlot a1 o1 _, .cellSlot a2 o2 _ => a1 != a2 || o1 != o2
  | .refCellTok a1 _ true, .refCellTok a2 _ true => a1 != a2
  | _, _ => true

abbrev Frag := Nat → Option Resource

def fragDisjoint (f1 f2 : Frag) : Prop :=
  ∀ k1 k2 r1 r2, f1 k1 = some r1 → f2 k2 = some r2 →
    k1 ≠ k2 ∧ resourceCompat r1 r2 = true

def fragUnion (f1 f2 : Frag) : Frag :=
  fun k => match f1 k with | some r => some r | none => f2 k

structure IProp where
  holds    : Frag → Prop
  upClosed : ∀ f1 f2, fragDisjoint f1 f2 → holds f1 → holds (fragUnion f1 f2)

def sepEmp : IProp :=
  { holds := fun _ => True, upClosed := fun _ _ _ h => h }

def sepConj (P Q : IProp) : IProp :=
  { holds := fun f => ∃ f1 f2, fragDisjoint f1 f2 ∧ P.holds f1 ∧ Q.holds f2 ∧
      ∀ k, f k = fragUnion f1 f2 k
    upClosed := ... }
```

This construction mirrors `JoJoDeveloping/tiny-iris` (`5b18c311e746d2ae4170b0d253b5d7d36ee5d6d9`, `theories/heapprop.v:7–10, 77–89`), where `heapProp` bundles `heapProp_holds : gmap loc val → Prop` with monotonicity `heapProp_closed` under map inclusion and collapses Iris's `later` modality to identity (`heapProp_later P := P` at `heapprop.v:117`).

To link `IProp` to operational evaluation without Iris ghost-state step-indexing, frame-quantified weakest preconditions quantify universally over all disjoint frames `F : IProp` (`theories/adequacy.v:9–46` in `tiny-iris`):

```coq
(* JoJoDeveloping/tiny-iris, theories/adequacy.v:9-10, 38 *)
Program Definition wpbigstep (e : expr) (Q : val → heapProp) : heapProp :=
  {| heapProp_holds σ := ∀ σ2, σ ##ₘ σ2 →
       ∃ v' σ', σ' ##ₘ σ2 ∧ ctx_steps e (σ ∪ σ2) (of_val v') (σ' ∪ σ2) ∧ Q v' σ' |}.

Lemma wp_soundness e Q : (⊢ wp e (λ v, ⌜Q v⌝))%I → ∀ σ, ∃ v σ', ctx_steps e σ (of_val v) σ' ∧ Q v.
```

In Lean 4, defining `sepWp prog Q fuel P st := ∀ F : IProp, Realizes (sepConj P F) st → wpState prog (fun out => ∃ f', (sepConj (Q out) F).holds f') fuel st` yields the Frame Rule immediately (by reassociating `F` with `R`) and discharges `wpState` adequacy by instantiating `F := sepEmp` (`adequacy.v:42`, setting `σ2 := ∅`).

---

### 2. Dual Obstructions Against Stored Heap Predicates: Kernel Positivity, Predicativity, and Cantor's Barrier

Basis: source + execution + derived

Consider adding a constructor storing a heap predicate directly inside `Resource`:

```lean
-- Rejected by Lean 4 kernel positivity and blocked by Cantor's theorem:
inductive BadResource where
  | cell       (alloc val : Nat)
  | storedPred (alloc : Nat) (inv : BadIProp)
```

where `BadIProp` is `IProp` over `BadFrag := Nat → Option BadResource`. Neither syntactic wrapping nor restricting predicates to upward-closed separation-logic propositions circumvents the barrier.

#### 2.1 Lean 4 Kernel Positivity and Universe Predicativity

Inspection of `leanprover/lean4` (`44db45ca210151a9fc25f10b8d7fa4535856680f`) `src/kernel/inductive.cpp` identifies two distinct kernel gates:

1. **Non-Positive Occurrence (`check_positivity`, `src/kernel/inductive.cpp:424–440`)**: Because `BadFrag : Type 0` (`Sort 1`) and `Prop : Type 0` (`Sort 1`), the function type `BadFrag → Prop` has sort `Sort (imax 1 1) = Type 0`, so `BadIProp : Type 0` as a standalone structure. However, `check_positivity` reduces each constructor field via WHNF and rejects any inductive occurrence inside a Pi domain (`src/kernel/inductive.cpp:428–431`):
   ```cpp
   } else if (is_pi(t)) {
       if (has_ind_occ(binding_domain(t)))
           throw kernel_exception(m_env, sstream() << "arg #" << (arg_idx + 1) << " of '" << cnstr_name << "' "
                                  "has a non positive occurrence of the datatypes being declared");
   ```
   Because `BadIProp.holds : (Nat → Option BadResource) → Prop` places `BadResource` left of `→`, any direct or parametric embedding raises this exception.
2. **Predicative Universe Level Check (`check_constructors`, `src/kernel/inductive.cpp:466–473`)**: For any inductive type at sort level `m_result_level` (`1` for `Type 0`), every constructor argument's type must have sort `s` satisfying:
   ```cpp
   if (!(is_geq(m_result_level, sort_level(s)) || normalizes_to_zero(m_result_level))) {
       throw kernel_exception(m_env, sstream() << "universe level of type_of(arg #" << (i + 1) << ") "
                              << "of '" << n << "' is too big for the corresponding inductive datatype");
   }
   ```
   While a plain `BadIProp : Type 0` hits positivity first, any attempt to store higher-universe objects—such as `Type`-valued existential witnesses (`Σ α : Type 0, P α : Type 1`) or COFE approximations (`Σ α : Type 0, COFE α : Type 1`)—has `sort_level(s) = 2 > 1 = m_result_level` and fails kernel predicativity.

#### 2.2 Constructive Cantor Diagonalization on Upward-Closed `IProp`

Even if positivity checks were bypassed axiomatically, **upward closure does not shrink `IProp` enough to embed into `Resource`**. Cantor's theorem holds constructively inside `Type 0` with zero axioms.

**Theorem (Upward-Closed Cantor Barrier).** *For any non-empty `Resource` and `Frag := Nat → Option Resource`, there exists no injection $\iota : \text{IProp} \to \text{Resource}$.*

*Proof.* Fix key `0 : Nat`. For every $D : \text{Resource} \to \text{Prop}$, define $U_D : \text{IProp}$ by:
$$U_D.\text{holds}(f) :\equiv \exists r : \text{Resource},\; f(0) = \text{some } r \land D(r)$$
`U_D` satisfies `upClosed` constructively: if `fragDisjoint f1 f2` and `f1 0 = some r`, then `(fragUnion f1 f2) 0 = match f1 0 with | some r => some r | none => f2 0 = some r`. Now suppose $\iota : \text{IProp} \to \text{Resource}$ were injective. Let $\delta(r) := \lambda k.\;\text{if } k = 0 \text{ then some } r \text{ else none}$ and define:
$$D^*(r) :\equiv \neg \bigl(\exists P : \text{IProp},\; \iota(P) = r \land P.\text{holds}(\delta(r))\bigr)$$
Setting $P^* := U_{D^*}$ and $r^* := \iota(P^*)$, `δ(r*) 0 = some r*` implies $P^*.\text{holds}(\delta(r^*)) \iff D^*(r^*)$. By injectivity of $\iota$, $\exists P,\, \iota(P) = r^* \land P.\text{holds}(\delta(r^*))$ reduces to $P^*.\text{holds}(\delta(r^*))$, yielding $P^*.\text{holds}(\delta(r^*)) \iff \neg P^*.\text{holds}(\delta(r^*))$—a direct contradiction. $\square$

Exhaustive Python enumeration over a 3-element carrier (`|Resource| = 3`, keys `{0, 1}`) confirms $2^3 = 8 > 3$ pairwise distinct upward-closed predicates $U_D$, with the diagonal $U_{D^*}$ strictly outside every candidate map `Resource → IProp`.

#### 2.3 Operational Manifestation: Landin's Knot and `RefCell` Borrow-Flag Dynamics

Landin's backpatching recursion idiom (Landin, 1964, DOI `10.1093/comjnl/6.4.308`) surfaces in Rust via interior mutability over trait-object closures (`Rc<RefCell<Option<Box<dyn Fn(u32) -> u32>>>>`):

```rust
use std::cell::RefCell;
use std::rc::Rc;

fn landins_countdown(n: u32, poison_reentrant_mut: bool) -> u32 {
    type RecFn = Rc<RefCell<Option<Box<dyn Fn(u32) -> u32>>>>;
    let slot: RecFn = Rc::new(RefCell::new(None));
    let slot_clone = Rc::clone(&slot);
    *slot.borrow_mut() = Some(Box::new(move |k: u32| {
        if k == 0 {
            0
        } else {
            if poison_reentrant_mut {
                let _g = slot_clone.borrow();       // BorrowCounter increments (> 0)
                *slot_clone.borrow_mut() = None;    // Panics: BorrowMutError
            }
            let guard = slot_clone.borrow();
            let f = guard.as_ref().unwrap();
            f(k - 1)                                // Indirect recursive call via heap slot
        }
    }));
    let g = slot.borrow();
    (g.as_ref().unwrap())(n)
}
```

Inspecting `rust-lang/rust` (`ec65cd52bba13d491ff65c9d218b39753755c84a`) `library/core/src/cell.rs:854–962, 1163–1280, 1561–1610, 2050–2093` explains the exact state machine:
- `RefCell<T>` tracks `borrow: Cell<BorrowCounter>` (`type BorrowCounter = isize`, `UNUSED = 0`, `is_reading(x) := x > 0`, `is_writing(x) := x < 0`).
- Backpatching `*slot.borrow_mut() = Some(...)` executes `BorrowRefMut::new` (`0 → -1` at `cell.rs:2066–2077`), stores the closure, and drops the temporary `RefMut` immediately (`-1 → 0` at `cell.rs:2057–2061`).
- Calling `(g.as_ref().unwrap())(n)` holds `let g = slot.borrow()` (`BorrowCounter = 1`), and each recursive step acquires an additional `BorrowRef` (`1 → 2 → ⋯ → n + 1`, valid while `< BorrowCounter::MAX` at `cell.rs:1564–1583`).
- When `poison_reentrant_mut = true`, `slot_clone.borrow_mut()` sees `borrow != UNUSED` (`cell.rs:2071–2077`), returning `Err(BorrowMutError)` and invoking `panic_already_borrowed` (`cell.rs:917–922`).
- Without step-indexing, stating an invariant $I(\text{slot})$ asserting that the closure inside `slot` expects $I(\text{slot})$ as its call precondition creates an unguarded circularity; non-terminating backpatching derives `False` (the naive invariant paradox; Reus & Schwinghammer, CSL 2006, DOI `10.1007/11874683_38`).

---

### 3. Cyclic First-Order `Rc<RefCell<Node>>` Graphs vs. Higher-Order Store

Basis: source + derived

Pointer cycles in the heap do **not** require step-indexing. Consider a cyclic singly-linked list `struct Node { val: u32, next: Option<Rc<RefCell<Node>>> }`:

1. **First-Order Graph Invariants (`Type 0`):** In `library/alloc/src/rcs/rc.rs:286–290`, `RcInner<RefCell<Node>>` (`#[repr(C, align(2))]`) stores `strong: Cell<usize>`, `weak: Cell<usize>`, and `value: RefCell<Node>`—purely first-order scalars and allocation IDs (`AllocId`). A finite graph invariant `GraphInv (nodes : List (AllocId × Nat × Option AllocId)) : IProp` forms the separating conjunction over each node's `rcHeader`, `refCellTok`, and (when not `.writing`) payload `cellSlot`. Self-edges or mutual cycles (`a.next = some b ∧ b.next = some a`) simply express `b ∈ dom(nodes)` and `a ∈ dom(nodes)`—pure first-order membership without storing `IProp` in `Resource`.
2. **Drop Reentrancy Protocol (`Rc::drop` / `drop_slow`):** At `library/alloc/src/rcs/rc.rs:2654–2662` and `405–417`, `Rc::drop` decrements `strong` (`1 → 0`) *before* calling `drop_slow`, where `drop_slow` anchors an implicit `_weak = Weak { ... }` (`rc.rs:409`) to keep the backing allocation alive during `ptr::drop_in_place` (`rc.rs:415`). Any cycle back-edge holding `Weak<RefCell<Node>>` that invokes `Weak::upgrade()` during recursive drop sees `strong == 0` and safely returns `None`. Modeling `rcHeader` with `RcDropState := .alive | .dropping | .deallocated` and extracting payload ownership before recursive drop proves reentrancy safety cleanly in unindexed `Type 0`.
3. **Stack-Scoped Higher-Order Closures (`Fn` / `FnMut` / `FnOnce`):** Generic functions `fn apply<F: FnMut(u32) -> u32>(f: &mut F, x: u32)` (`library/core/src/ops/function.rs:76–180`) monomorphize to concrete stack environments and parameterize over abstract Lean predicates `(Inv : Env → IProp)` externally—never storing `IProp` inside `Frag`.

| Rust / Verification Idiom | Fits Unindexed `Type 0` `IProp`? | Technical Reason |
|---|---|---|
| Raw pointers, `split_at_mut`, `MaybeUninit`, byte `transmute` | **Yes (Native)** | First-order `(AllocId, offset)` ranges and byte sequences. |
| Aliased `&Cell<T>`, `&[Cell<u8>]`, branded `GhostCell<'id, T>` | **Yes (Native)** | First-order `Val → Prop` invariants or branded linear tokens (Yanovski et al., ICFP 2021). |
| `RefCell<T>`, `Ref<'a, T>`, `RefMut<'a, T>`, `OnceCell<T>` | **Yes (Native)** | Borrow-counter state machines + persistent post-init witnesses. |
| **Cyclic `Rc<RefCell<Node>>`, `Weak<T>`, doubly-linked lists** | **Yes (Native)** | Graph invariant quantifies over finite `AllocId → NodeData` tables; zero stored `IProp`. |
| `Mutex<Data>`, `RwLock<Data>`, `SeqLock<Data>` (first-order `Data`) | **Yes (Native)** | Epoch counters (`Nat`) + first-order data predicates. |
| **Stack-scoped generic closures `fn apply<F: FnMut(T) -> U>(f: &mut F)`** | **Yes (Native)** | Externally quantified Lean pre/post predicates over concrete stack environment `Env`. |
| **Landin's knot `Rc<RefCell<Option<Box<dyn Fn(u32) -> u32>>>>`** | **NO (Crosses Barrier)** | Stored `dyn Fn` precondition references `Rc<RefCell<...>>`'s own stored invariant. |
| **Reentrant heterogeneous queues `Arc<Mutex<Vec<Box<dyn FnOnce() + Send>>>>`** | **NO (Crosses Barrier)** | Queued closures may capture handles back to the queue lock, requiring saved predicates. |
| **Open mutably swappable `RawWakerVTable` state machines** | **NO (Crosses Barrier)** | Open vtables store recursive contracts across arbitrary future `wake`/`poll` reentries. |

---

### 4. Iris COFE Banach Fixpoints vs. Lean 4 Kernel Physics

Basis: source + documentation + derived

Full higher-order separation logic (`Iris`; Jung et al., JFP 2018, DOI `10.1017/S0956796818000151`; Birkedal et al., POPL 2011, DOI `10.1145/1925844.1926401`; Appel & McAllester, TOPLAS 2001, DOI `10.1145/504709.504712`; Nakano, LICS 2000, DOI `10.1109/LICS.2000.855774`) resolves the recursive equation $\text{iProp} \cong \text{UPred}(\text{Res}(\triangleright\,\text{iProp}))$ using ultrametric Banach fixpoints. Inspecting `leanprover-community/iris-lean` (`5540ef0110fc8f6d8e495c10c2f238c3ede14f3b`; de Medeiros et al., 2026, DOI `10.48550/arXiv.2609.24252`) highlights the exact Lean 4 infrastructure and its costs:

1. **Ordered Families of Equivalences (`Iris/Iris/Algebra/OFE.lean:17–44`)**: `class OFE (α : Type _)` defines indexed step equivalences `Dist : Nat → α → α → Prop` (`x ≡{n}≡ y`) satisfying `eq_dist' : x = y ↔ ∀ n, Dist n x y`.
2. **Uniform Predicates (`Iris/Iris/Algebra/UPred.lean:19–43, 83–125, 165–170`)**: `UPred M` couples `holds : (n : Nat) → ValidAt M n → Prop` with combined step-downward and resource-upward monotonicity `mono`, plus completeness `IsCOFE (UPred M)` (`compl c := ∀ n', n' ≤ n → (c n') n' (x.le Hle)` at `UPred.lean:117`).
3. **Universe-Polymorphic Inverse-Limit `COFESolver` (`Iris/Iris/Algebra/COFESolver.lean:26–106, 265–340`)**: Starting from `A' : Nat → Σ α : Type u, COFE α` (`COFESolver.lean:26–28`), Iris-Lean constructs linear `O(k)` embeddings `updown` (`COFESolver.lean:41–43`), forms the inverse-limit `Tower : Type u` (`COFESolver.lean:73–75`), proves `COFE (Tower F)` (`COFESolver.lean:99–105`), and seals `opaque Tower.iso : OFE.Iso (F (Tower F) (Tower F)) (Tower F)` (`COFESolver.lean:315`) providing `Fix.fold` and `Fix.unfold` (`COFESolver.lean:331–338`).

For lightweight `Type 0` Rust verifiers, adopting `COFESolver` carries three costs:
- **Universe Polymorphism:** `OFE (α : Type _)` and `Σ α : Type u, COFE α` (`COFESolver.lean:26`) require universe-polymorphic `Type u` declarations, incompatible with strict monomorphic `Type 0` kernel audits.
- **Extensionality Axioms:** `Tower.ext_iff` (`COFESolver.lean:87`) and `UPred` `eq_dist'` (`UPred.lean:91`) invoke `funext` (`Quot.sound`) and `propext` routinely during separation-logic equality proofs (`least_fixpoint_unfold` at `Iris/Iris/BI/Lib/Fixpoint.lean:86–88`).
- **Tactic and Proof Overhead:** Every first-order specification inherits `NonExpansive` obligations and `▷`-stripping steps even when no stored closures exist.

---

### 5. Dual `Type 0` Solutions Without COFEs: Defunctionalization and Fuel-Indexed `StepIProp`

Basis: source + execution + derived

Two strictly `Type 0` techniques resolve stored closures inside partial-correctness operational verifiers without COFEs or universe polymorphism.

#### 5.1 Closed-Crate Defunctionalization (`InvCode := DefId × Val`)

When verifying a closed Rust crate (`Program.bodies`), the set of closure functions and trait-object vtables is statically finite. Following Reynolds's defunctionalization (1972, DOI `10.1145/800194.805852`), store a first-order **closure code** instead of an `IProp`:

```lean
abbrev DefId := Nat

inductive Val where
  | scalar (n : Nat)
  | ptr    (alloc off : Nat)
  | pair   (fst snd : Val)
  | none

structure InvCode where
  fnId : DefId
  env  : Val

-- Strictly positive in Type 0: Resource stores only DefId × Val!
inductive DefuncResource where
  | cellSlot   (alloc off : Nat) (v : Val)
  | refCellTok (alloc : Nat) (flag : Int) (code : Option InvCode)
  | rcHeader   (alloc strong weak : Nat)
```

Because `InvCode : Type 0` mentions no predicate type, Lean 4 accepts `DefuncResource : Type 0` immediately. An external dispatch interpreter parameterized by call fuel `k : Nat`:

```lean
def interpInvCode (dispatch : DefId → Val → Val → (Val → IProp) → IProp) :
    Nat → InvCode → Val → IProp
  | 0,     _,    _   => sepEmp
  | k + 1, code, arg =>
      dispatch code.fnId code.env arg (fun nextArg => interpInvCode dispatch k code nextArg)
```

terminates structurally on `k` whenever indirect calls consume $\ge 1$ operational step (`ProductiveInvariant`). Standalone `InvCode` suffices when the closed crate's call graph is bounded statically, though open-world library traits require dynamic callers' specifications.

#### 5.2 Fuel-Indexed `StepIProp := Nat → IProp` and Partial-Correctness Adequacy

Operational verifiers using functional big-step or fuel-indexed small-step interpreters (Owens et al., ESOP 2016, DOI `10.1007/978-3-662-49498-1_23`) *already* thread `fuel : Nat` through `wpState` (`@Nat.rec`) to guarantee total kernel termination. Indexing `IProp` by that same `Nat` step budget produces a constructive `Type 0` step-indexed separation logic:

```lean
namespace FuelIndexedSL

open UnindexedSL

def StepIProp : Type := Nat → IProp

def stepEmp  : StepIProp := fun _ => sepEmp
def stepTrue : StepIProp := fun _ => { holds := fun _ => True, upClosed := fun _ _ _ h => h }
def stepSep (P Q : StepIProp) : StepIProp := fun k => sepConj (P k) (Q k)

def stepLater (P : StepIProp) : StepIProp :=
  fun k => match k with
    | 0     => stepTrue 0
    | k + 1 => P k

def stepEntailsAt (k : Nat) (P Q : StepIProp) : Prop :=
  ∀ f, (P k).holds f → (Q k).holds f

-- Constructive Löb induction directly via Nat.rec (zero COFEs, zero extra axioms):
theorem step_loeb (P : StepIProp)
    (h : ∀ k, stepEntailsAt k (stepLater P) P) :
    ∀ k, stepEntailsAt k stepEmp P := by
  intro k
  induction k with
  | zero      => intro f _; exact h 0 f True.intro
  | succ k ih => intro f hf; exact h (k + 1) f (ih f hf)
```

Requiring frame predicates `F : StepIProp` to be downward-closed in fuel (`downClosed F : ∀ k1 k2 f, k2 ≤ k1 → (F k1).holds f → (F k2).holds f`) guarantees any outer frame preserved across a step reducing fuel `k + 1 → k` remains valid at `k`. Synchronizing `stepWp` with the operational fuel counter:

```lean
def stepWp (prog : Prog) (Q : Out → StepIProp) (onFault : Fault → Prop)
    (fuel : Nat) (P : StepIProp) (st : State) : Prop :=
  ∀ (F : StepIProp), downClosed F →
    Realizes (sepConj (P fuel) (F fuel)) st →
    wpState prog (fun out => ∃ f', (sepConj (Q out out.remFuel) (F out.remFuel)).holds f')
      onFault fuel st
```

yields three guarantees for `landins_countdown`:
1. **Lockstep Guarded Unfolding:** Each recursive closure call `f(k - 1)` decrements operational fuel `fuel' + 1 → fuel'`, discharging `stepLater Inv (fuel' + 1) = Inv fuel'` cleanly without COFEs or Banach fixpoints.
2. **Partial-Correctness Adequacy (`F := stepEmp`):** For any input `n` and any sufficient fuel `fuel` where execution terminates before fuel exhaustion, `stepWp` implies `wpState prog (fun out => Q_unindexed out) (fun _ => False) fuel initState`, proving `out = 0` when `poison_reentrant_mut = false` with zero undefined behavior.
3. **Deterministic Borrow-Panic Attribution:** When `poison_reentrant_mut = true`, `BorrowCounter` is `1` at `slot_clone.borrow_mut()`, forcing transition into the `BorrowMutError` fault/panic branch rather than failing soundness.

Combining `InvCode := DefId × Val` (inside `Resource : Type 0`) with `StepIProp := Nat → IProp` (for the invariant semantics `interpInvCode`) handles closed-crate Landin's-knot closures entirely within axiom-minimal, monomorphic `Type 0` Lean 4.

## Boundaries

- **known not to apply** (Total correctness and non-terminating liveness): Fuel-indexed `StepIProp := Nat → IProp` establishes *partial correctness* for every finite execution trace terminating within `fuel` steps (`remFuel > 0`). It cannot verify unbounded termination or fair liveness (`Diverges` / `Eventually` properties) of arbitrary cyclic task schedulers without transfinite ordinals (Spies et al., PLDI 2021, DOI `10.1145/3453483.3454031`).
- **unsupported** (Open-world separate compilation under `InvCode`): Pure `InvCode := DefId × Val` defunctionalization cannot verify crates holding opaque dynamically linked `Box<dyn Fn>` callbacks whose implementations are absent from `Program.bodies`; open higher-order boundaries require abstract caller invariant parameters or full `iris-lean` COFEs.
- **not examined** (Weak-memory atomic closure publication): Cross-thread publication via `Arc<AtomicPtr<Box<dyn Fn()>>>` with `Acquire`/`Release`/`Relaxed` memory orderings (outside mutex-protected sequentialization) was not examined.
- **unknown** (Kernel WHNF crossover on large closed crates): While finite-fuel `StepIProp` and `InvCode` validate cleanly on small models (`n ≤ 5` countdown checks), the exact elaboration and kernel-reduction crossover between large `InvCode` match tables and `iris-lean` `COFESolver` towers on crates exceeding $1{,}000$ distinct closure bodies remains unmeasured.

## Evidence

| Artifact / Claim | Source / Publication | Exact Immutable Identity & Location | Role |
|---|---|---|---|
| Lean 4 `check_positivity` and `check_constructors` universe check | `leanprover/lean4` | `44db45ca210151a9fc25f10b8d7fa4535856680f`, `src/kernel/inductive.cpp:424–440, 466–473` | `source` |
| Iris-Lean `OFE`, `UPred`, `IsCOFE`, `COFESolver` (`A'`, `updown`, `Tower`, `Fix.iso`), and `Fixpoint` | `leanprover-community/iris-lean` | `5540ef0110fc8f6d8e495c10c2f238c3ede14f3b`, `Iris/Iris/Algebra/{OFE.lean:17–44, UPred.lean:19–170, COFESolver.lean:26–340}`, `Iris/Iris/BI/Lib/Fixpoint.lean:18–95`; de Medeiros et al. (2026), DOI `10.48550/arXiv.2609.24252` | `source` + `documentation` |
| Tiny-Iris `heapProp`, `heapProp_later`, `wpbigstep`, and `wp_soundness` (`σ2 := ∅`) | `JoJoDeveloping/tiny-iris` | `5b18c311e746d2ae4170b0d253b5d7d36ee5d6d9`, `theories/{heapprop.v:7–254, weakestpre.v:6–111, adequacy.v:9–54}` | `source` |
| Rust `RefCell`, `BorrowCounter`, `BorrowRef`, `BorrowRefMut`, `RcInner`, `Rc::drop` / `drop_slow`, `Fn`/`FnMut`/`FnOnce` | `rust-lang/rust` | `ec65cd52bba13d491ff65c9d218b39753755c84a`, `library/core/src/cell.rs:854–962, 1163–1280, 1561–1610, 2050–2093`, `library/alloc/src/rcs/rc.rs:286–290, 405–417, 2654–2662`, `library/core/src/ops/function.rs:76–180` | `source` |
| Aeneas Rust-to-Lean functional translation architecture | `AeneasVerif/aeneas` | `2e3d4488280bb8a95411db81019a7854a784861f`; Ho & Protzenko (ICFP 2022), DOI `10.1145/3547647` | `source` + `documentation` |
| Peer-reviewed foundational literature | Formal methods literature | Landin (1964) `10.1093/comjnl/6.4.308`; Reynolds (1972) `10.1145/800194.805852`; Nakano (2000) `10.1109/LICS.2000.855774`; Appel & McAllester (2001) `10.1145/504709.504712`; Reus & Schwinghammer (2006) `10.1007/11874683_38`; Birkedal et al. (2011) `10.1145/1925844.1926401`; Owens et al. (2016) `10.1007/978-3-662-49498-1_23`; Jung et al. (2018) `10.1017/S0956796818000151`; Spies et al. (2021) `10.1145/3453483.3454031`; Yanovski et al. (2021) `10.1145/3473597` | `normative` + `documentation` |
| Constructive Cantor diagonal & finite-fuel `StepIProp` oracle (2026-11-20) | Local Python 3.13 verification run | Finite carrier (`|Resource| = 3`, keys `{0,1}`): `distinct_upward_closed_UD = 8 > 3`; diagonal `P* = U_{D*}` strictly outside candidate map `iota`; `step_loeb` verified to `fuel = 16`; `landins_countdown(n, false)` returns `("OK", 0)` for `n ∈ 0..5`; `landins_countdown(1, true)` detects `("BORROW_MUT_PANIC", -1)`; `landins_countdown(5, 3)` returns `("FUEL_EXHAUSTED", 0)` | `execution` |

## Revalidation

1. **Lean 4 Kernel Rejection Check**: Feed `inductive BadRes : Type 0 where | pred : ((Nat → Option BadRes) → Prop) → BadRes` (and `inductive BadSize : Type 0 where | wrap : (Σ α : Type 0, α → Prop) → BadSize`) to `lean --stdin` and verify `src/kernel/inductive.cpp:424–473` rejects non-positive Pi domains and `Type 1` constructor arguments inside `Type 0`.
2. **Upward-Closed Cantor & Fuel-Indexed Löb Revalidation Probe** (Python 3.10+, `< 10 ms`):
   ```bash
   python3 - <<'PY'
   R, K = (0, 1, 2), (0, 1)
   frags = [(a, b) for a in (None, *R) for b in (None, *R)]
   disj = lambda f1, f2: all(not (f1[k] is not None and f2[k] is not None) for k in K)
   union = lambda f1, f2: tuple(f1[k] if f1[k] is not None else f2[k] for k in K)
   u_preds = []
   for mask in range(1 << len(R)):
       sub = {r for r in R if (mask >> r) & 1}
       sat = frozenset(f for f in frags if f[0] in sub)
       assert all(union(f1, f2) in sat for f1 in sat for f2 in frags if disj(f1, f2))
       u_preds.append(sat)
   assert len(set(u_preds)) == 2 ** len(R) > len(R)
   iota = {0: u_preds[0], 1: u_preds[3], 2: u_preds[7]}
   p_star = frozenset(f for f in frags if f[0] in {r for r in R if (r, None) not in iota[r]})
   assert p_star not in iota.values()
   p = {0: True}
   for k in range(1, 17):
       p[k] = p[k - 1]
   assert all(p.values())
   print("REVALIDATION_OK", len(set(u_preds)), len(R))
   PY
   ```
3. **Upstream Diff Check**: Diff `src/kernel/inductive.cpp` (`leanprover/lean4`), `Iris/Iris/Algebra/{UPred,COFESolver}.lean` (`leanprover-community/iris-lean`), and `library/core/src/cell.rs` + `library/alloc/src/rcs/rc.rs` (`rust-lang/rust`) against the pinned revisions in `REPORT.json`.
