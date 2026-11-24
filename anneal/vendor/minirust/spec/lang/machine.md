# MiniRust Abstract Machine

This defines the state that makes up the MiniRust Abstract Machine:
which components together make up the state of a MiniRust program during its execution?
This key data structure says a lot about how the Abstract Machine is structured.

The "reduction relation" aka operational semantics is defined by the `step` function below,
which is defined in terms of many [evaluation functions for our various syntactic categories](step/).

```rust
/// This type contains everything that needs to be tracked during the execution
/// of a MiniRust program.
#[no_obj]
pub struct Machine<M: Memory> {
    /// The program we are executing.
    prog: Program,

    /// The contents of memory.
    mem: ConcurrentMemory<M>,

    /// The state of the integer-pointer cast subsystem.
    intptrcast: IntPtrCast<M::Provenance>,

    /// The threads (in particular, their stacks).
    threads: List<Thread<M>>,

    /// The currently / most recently active thread.
    active_thread: ThreadId,

    /// A set of threads that have been synchronized.
    /// A thread being added here in a given step means that if the very next step is
    /// by that thread, we do *not* do data race detection: there was synchronization
    /// between these two steps, so any potential accesses are not racing.
    synchronized_threads: Set<ThreadId>,

    /// The Locks
    locks: List<LockState>,

    /// Stores a pointer to each of the global allocations, which are all `Sized`.
    global_ptrs: Map<GlobalName, ThinPointer<M::Provenance>>,

    /// Stores a pointer for each function name.
    fn_ptrs: Map<FnName, ThinPointer<M::Provenance>>,

    /// Stores a pointer for each vtable.
    vtable_ptrs: Map<VTableName, ThinPointer<M::Provenance>>,

    /// This is where the `PrintStdout` intrinsic writes to.
    stdout: DynWrite,
    /// This is where the `PrintStderr` intrinsic writes to.
    stderr: DynWrite,
}

/// The data that makes up a stack frame.
struct StackFrame<M: Memory> {
    /// The function this stack frame belongs to.
    func: Function,

    /// For each live local, the location in memory where its value is stored.
    locals: Map<LocalName, ThinPointer<M::Provenance>>,

    /// Expresses what happens after the callee (this function) returns or resumes unwinding.
    stack_pop_action: StackPopAction<M>,

    /// `next_block` and `next_stmt` describe the next statement/terminator to execute (the "program counter").
    /// `next_block` identifies the basic block,
    next_block: BbName,

    /// If `next_stmt` is equal to the number of statements in this block (an
    /// out-of-bounds index in the statement list), it refers to the terminator.
    next_stmt: Int,

    /// The memory model is given the ability to track some extra per-frame data.
    extra: M::FrameExtra,
}

/// Defines the behavior when the function returns or resumes unwinding.
enum StackPopAction<M: Memory> {
    /// This is the bottom of the stack, there is nothing left to do in this thread.
    BottomOfStack,
    /// Go back to the caller.
    BackToCaller {
        /// The basic block to jump to when the callee returns.
        /// If `None`, UB will be raised when the callee returns.
        next_block: Option<BbName>,
        /// The basic block to jump to when the callee resumes unwinding.
        /// If `None`, UB will be raised when the callee resumes unwinding.
        unwind_block: Option<BbName>,
        /// The location where the caller wants to see the return value.
        /// The caller type already been checked to be suitably compatible with the callee return type.
        ret_val_ptr: ThinPointer<M::Provenance>,
    },
}
```

This defines the internal representation of a thread of execution.

```rust
pub struct Thread<M: Memory> {
    /// The stack. This is only the "control" part of the stack; the "data" part
    /// lives in memory (and stack and memory are completely disjoint concepts
    /// in the Abstract Machine).
    stack: List<StackFrame<M>>,

    /// Stores whether the thread is ready to run, blocked, or terminated.
    state: ThreadState,

    /// Stores the unwind payloads.
    unwind_payloads: List<ThinPointer<M::Provenance>>,
}

pub enum ThreadState {
    /// The thread is enabled and can get executed.
    Enabled,
    /// The thread is trying to join another thread and is blocked until that thread finishes.
    BlockedOnJoin(ThreadId),
    /// The thread is waiting to acquire a lock.
    BlockedOnLock(LockId),
    /// The thread has terminated.
    Terminated,
}
```

Next, we define the core operations of every (state) machine: the initial state, and the transition function.
The transition function simply dispatches to evaluating the next statement/terminator.

```rust
impl<M: Memory> Machine<M> {
    pub fn new(prog: Program, mem_params: M::Params, stdout: DynWrite, stderr: DynWrite) -> NdResult<Machine<M>> {
        prog.check_wf::<M::T>()?;

        let mut mem = ConcurrentMemory::<M>::new(mem_params);
        let mut global_ptrs = Map::new();
        let mut fn_ptrs = Map::new();
        let mut vtable_ptrs = Map::new();

        // Allocate every global.
        for (global_name, global) in prog.globals {
            let size = Size::from_bytes(global.bytes.len()).unwrap();
            let alloc = mem.allocate(AllocationKind::Global, size, global.align)?;
            global_ptrs.insert(global_name, alloc);
        }

        // Fill the allocations.
        for (global_name, global) in prog.globals {
            let mut bytes = global.bytes.map(|b|
                match b {
                    Some(x) => AbstractByte::Init(x, None),
                    None => AbstractByte::Uninit
                }
            );
            for (i, relocation) in global.relocations {
                let ptr = global_ptrs[relocation.name].wrapping_offset::<M::T>(relocation.offset.bytes());
                let encoded_ptr = encode_ptr::<M>(ptr);
                bytes.write_subslice_at_index(i.bytes(), encoded_ptr);
            }
            // This cannot fail, we just allocated that memory above.
            mem.store(global_ptrs[global_name], bytes, global.align, Atomicity::None).unwrap();
        }

        // Allocate functions.
        for (fn_name, _function) in prog.functions {
            let alloc = mem.allocate(AllocationKind::Function, Size::ZERO, Align::ONE)?;
            fn_ptrs.insert(fn_name, alloc);
        }

        // Allocate vtables.
        for (vtable_name, _vtable) in prog.vtables {
            let alloc = mem.allocate(AllocationKind::VTable, Size::ZERO, Align::ONE)?;
            vtable_ptrs.insert(vtable_name, alloc);
        }

        // Create machine, without a thread yet.
        let mut machine = Machine {
            prog,
            mem,
            intptrcast: IntPtrCast::new(),
            global_ptrs,
            fn_ptrs,
            vtable_ptrs,
            threads: list![],
            locks: List::new(),
            active_thread: ThreadId::ZERO,
            synchronized_threads: Set::new(),
            stdout,
            stderr,
        };

        // Create initial thread.
        let start_fn = prog.functions[prog.start];
        machine.new_thread(start_fn, list![])?;

        ret(machine)
    }

    /// To run a MiniRust program, call this in a loop until it throws an `Err` (UB or termination).
    pub fn step(&mut self) -> NdResult {
        if !self.threads.any( |thread| thread.state == ThreadState::Enabled ) {
            throw_deadlock!();
        }

        // Reset the data race tracking *before* we change `active_thread`.
        let prev_step_information = self.reset_data_race_tracking();

        // Update current thread.
        let distr = libspecr::IntDistribution {
            start: Int::ZERO,
            end: Int::from(self.threads.len()),
            divisor: Int::ONE,
        };
        self.active_thread = pick(distr, |id: ThreadId| {
            let Some(thread) = self.threads.get(id) else {
                return false;
            };

            thread.state == ThreadState::Enabled
        })?;

        // Execute this step.
        let frame = self.cur_frame();
        let block = &frame.func.blocks[frame.next_block];
        if frame.next_stmt == block.statements.len() {
            // It is the terminator. Evaluating it will update `frame.next_block` and `frame.next_stmt`.
            self.eval_terminator(block.terminator)?;
        } else {
            // Bump up PC, evaluate this statement.
            let stmt = block.statements[frame.next_stmt];
            self.eval_statement(stmt)?;
            self.try_mutate_cur_frame(|frame, _mem| {
                frame.next_stmt += 1;
                ret(())
            })?;
        }

        // Check for data races with the previous step.
        self.mem.check_data_races(self.active_thread, prev_step_information)?;

        ret(())
    }
}
```

We also define some general helper functions for working with threads and stack frames.

```rust
impl<M: Memory> Machine<M> {
    fn active_thread(&self) -> Thread<M> {
        self.threads[self.active_thread]
    }

    fn mutate_active_thread<O>(&mut self, f: impl FnOnce(&mut Thread<M>) -> O) -> O {
        self.threads.mutate_at(self.active_thread, f)
    }

    fn cur_frame(&self) -> StackFrame<M> {
        self.active_thread().cur_frame()
    }

    fn mutate_cur_frame<O>(&mut self, f: impl FnOnce(&mut StackFrame<M>, &mut ConcurrentMemory<M>) -> O) -> O {
        self.threads.mutate_at(self.active_thread, |thread| thread.mutate_cur_frame(|frame| f(frame, &mut self.mem)))
    }

    fn try_mutate_cur_frame<O>(&mut self, f: impl FnOnce(&mut StackFrame<M>, &mut ConcurrentMemory<M>) -> NdResult<O>) -> NdResult<O> {
        self.threads.try_mutate_at(self.active_thread, |thread| thread.try_mutate_cur_frame(|frame| f(frame, &mut self.mem)))
    }

    fn mutate_cur_stack<O>(&mut self, f: impl FnOnce(&mut List<StackFrame<M>>) -> O) -> O {
        self.threads.mutate_at(self.active_thread, |thread| f(&mut thread.stack))
    }
}

impl<M: Memory> Thread<M> {
    fn cur_frame(&self) -> StackFrame<M> {
        self.stack.last().unwrap()
    }

    fn mutate_cur_frame<O>(&mut self, f: impl FnOnce(&mut StackFrame<M>) -> O) -> O {
        if self.stack.is_empty() {
            panic!("`mutate_cur_frame` called on empty stack!");
        }

        let last_idx = self.stack.len() - 1;
        self.stack.mutate_at(last_idx, f)
    }

    fn try_mutate_cur_frame<O>(&mut self, f: impl FnOnce(&mut StackFrame<M>) -> NdResult<O>) -> NdResult<O> {
        if self.stack.is_empty() {
            panic!("`try_mutate_cur_frame` called on empty stack!");
        }

        let last_idx = self.stack.len() - 1;
        self.stack.try_mutate_at(last_idx, f)
    }
}

impl<M: Memory> StackFrame<M> {
    /// jump to the beginning of the given block.
    fn jump_to_block(&mut self, b: BbName) {
        self.next_block = b;
        self.next_stmt = Int::ZERO;
    }
}
```

Some higher-level helper functions that do not have a better location.

```rust
impl<M: Memory> Machine<M> {
    /// Create a new thread where the first frame calls the given function with the given arguments.
    fn new_thread(&mut self, func: Function, args: List<(Value<M>, Type)>) -> NdResult<ThreadId> {
        // The bottom of a stack must have a 1-ZST return type.
        // This way it cannot assume there is actually a return place to write anything to.
        let init_frame = self.create_frame(
            func,
            StackPopAction::BottomOfStack,
            CallingConvention::C,
            unit_type(),
            args,
        )?;
        // Push the new thread, return the index.
        let thread = Thread {
            state: ThreadState::Enabled,
            stack: list![init_frame],
            unwind_payloads: list![],
        };
        let thread_id = ThreadId::from(self.threads.len());
        self.threads.push(thread);
        ret(thread_id)
    }

    /// Look up a function given a pointer.
    fn fn_from_ptr(&self, ptr: Value<M>) -> Result<Function> {
        if let Value::Ptr(Pointer { thin_pointer: thin_ptr, metadata }) = ptr {
            if metadata.is_some() {
                throw_ub!("invalid pointer for function lookup");
            }
            let Some((func_name, _)) = self.fn_ptrs.iter().find(|(_, fn_ptr)| *fn_ptr == thin_ptr) else {
                throw_ub!("invalid pointer for function lookup");
            };
            ret(self.prog.functions[func_name])
        } else {
            throw_ub!("trying to look up a function based on a non-pointer value");
        }
    }

    /// Look up a vtable given a pointer.
    fn vtable_from_ptr(&self, ptr: ThinPointer<M::Provenance>) -> Result<VTable> {
        let Some((vtable_name, _)) = self.vtable_ptrs.iter().find(|(_, vtable_ptr)| *vtable_ptr == ptr) else {
            throw_ub!("invalid pointer for vtable lookup");
        };
        ret(self.prog.vtables[vtable_name])
    }

    /// Reset the data race tracking for the next step, and return the information from the previous step.
    ///
    /// The first component of the return value is the set of threads that were synchronized by the previous step,
    /// the second is the list of accesses in the previous step.
    fn reset_data_race_tracking(&mut self) -> (Set<ThreadId>, List<Access>) {
        // Remember threads synchronized by the previous step for data race detection
        // after this step.
        let mut prev_sync = self.synchronized_threads;
        // Every thread is always synchronized with itself.
        prev_sync.insert(self.active_thread);

        // Reset access tracking list.
        let prev_accesses = self.mem.reset_accesses();

        (prev_sync, prev_accesses)
    }

    /// All vtable lookups must have well-defined pointers. If this panics it is a spec bug.
    fn vtable_lookup(&self) -> impl Fn(ThinPointer<M::Provenance>) -> VTable + 'static {
        // This copies the data to return a static closure, as it is used in mutate functions, which mutably borrow self.
        let ptrs = self.vtable_ptrs;
        let vtables = self.prog.vtables;
        move |ptr| {
            let (name, _) = ptrs.iter().find(|(_, vtable_ptr)| *vtable_ptr == ptr).unwrap();
            let vtable = vtables[name];
            vtable
        }
    }

    /// Helper function to compute the size with the allocated vtables in `self`.
    fn compute_size(&self, layout: LayoutStrategy, meta: Option<PointerMeta<M::Provenance>>) -> Size {
        let (size, _) = layout.compute_size_and_align(meta, self.vtable_lookup());
        size
    }

    /// Helper function to compute the alignment with the allocated vtables in `self`.
    fn compute_align(&self, layout: LayoutStrategy, meta: Option<PointerMeta<M::Provenance>>) -> Align {
        let (_, align) = layout.compute_size_and_align(meta, self.vtable_lookup());
        align
    }
}
```
