# Superdense logical time, hybrid synchronous causality, and SRP-based preemptive interrupt verification

## Summary

This report characterises how seven lines of work treat the seam between deterministic logical time and
asynchronous hardware events, and what each one actually proves.

- **Superdense tags (Lingua Franca C runtime).** A tag is `(int64 time in ns, uint32 microstep)` ordered
  lexicographically. A zero delay yields `(t, m+1)`; a positive delay `d` yields `(t+d, 0)`. Tag delay is
  therefore not additive (`delay(delay(g,0),d) != delay(delay(g,d),0)`), and the two arithmetic entry points
  disagree on microstep overflow: `lf_delay_tag` wraps (inverting the order), `lf_tag_add` saturates to
  `FOREVER_TAG`.
- **Admission of asynchronous events.** A physical action is stamped, under the environment lock, with
  `physical clock + min_delay + extra_delay`, microstep 0, then adjusted by a minimum-spacing policy
  (`defer`, `drop`, `replace`, and in source also `update`) and finally bumped one microstep if it equals the
  current tag. Determinism is determinism *given the assigned tags*; the tag assignment itself, and the lazy
  deadline check, are physical-time dependent.
- **Mechanised reactor model (Lean 4).** Determinism of execution is proved; finite variability is proved
  *false* for the model (a reaction can reschedule itself at the same time forever, advancing only the
  microstep), while a weaker per-time-point bound holds. The model has no physical time.
- **Causality.** Vélus checks one acyclic dependency graph per node and treats every node instance as
  atomic (each output depends on every argument). Zélus infers a polymorphic causality type scheme with
  strict-order constraints per declaration and stores it in the module's value environment next to the
  ordinary type scheme; `pre`, the delayed
  argument of `fby`, and `up(.)` cut instantaneous dependencies; `atomic` collapses a node to the Vélus
  discipline. The Zélus simulation loop cascades discrete steps at one instant until the horizon moves.
- **Stack Resource Policy on interrupt hardware (RTIC 2.4.0).** A resource ceiling is the maximum priority
  of the tasks that access it; `lock` raises `BASEPRI` to the ceiling (or masks a compile-time interrupt set
  where `BASEPRI` is absent) around a closure. An exhaustive small-model run reproduces the SRP properties
  (no deadlock, at most one blocking critical section per job, no blocking after start, LIFO resumption)
  and shows plain mutexes and priority inheritance violating each of them.
- **Lost wake-ups.** Three independent code bases (RTIC's async executor, the seL4 device-driver
  framework's shared-queue signalling, and the Lingua Franca bare-metal sleep) rely on the same discipline:
  a latching, coalescing notification plus "clear or arm first, then re-examine the condition". Explicit-state
  exploration shows each reordering loses a wake-up.
- **Negative space.** None of the mechanised artifacts examined proves preemptive interrupt-handler code
  end to end: the Bedrock2/Kami system polls; Pancake models device access as foreign-call events and its
  compiler theorem covers `main` only; Prosa 0.6 offers response-time analyses parameterised by a
  preemption model, not by resource ceilings; RefinedProsa targets interrupt-free schedulers.

## Applicability

The subjects in `REPORT.json` are compared, not composed. No claim is made that they interoperate.

- **Lingua Franca.** Runtime findings apply to the C runtime `lf-lang/reactor-c` at commit
  `abbf0aaf468af55f298e1ae4816156e9f7552784`, threaded and single-threaded variants as stated. Compiler
  and verifier findings apply to `lf-lang/lingua-franca` at `0df8a987e37d6bc0cc8daa1c3e6167df14eaae59`
  (`gradle.properties` version `0.14.0-SNAPSHOT`). Handbook statements were read from the published
  handbook labelled version 0.13.0; where handbook and source differ, both are reported. The C++, Rust,
  Python, TypeScript and micro-C runtimes and federated execution were not examined.
- **Reactor model.** `marcusrossel/reactor-model` at `7a7d1f36ba5b908f2d3744f8cd08186eac325fe6`
  (Lean toolchain `leanprover/lean4:v4.24.0-rc1`). Theorem statements were read; the development was not
  rebuilt.
- **Zélus / Vélus.** `INRIA/zelus` at `5f6e4903103e136f52cdcefc13a9bdcff0f53abd` and `INRIA/velus` at
  `27ba860c2624ba232816591290c6c119b9ead88a` (README states Coq 8.20.1). Source and theorem statements
  were read; neither compiler was built or run.
- **RTIC.** `rtic-rs/rtic` at `fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9` (`rtic` crate 2.4.0), Cortex-M
  back ends `cortex_basepri.rs` and `cortex_source_mask.rs`. RISC-V back ends, `rtic-sync` and
  `rtic-monotonics` were not examined. No RTIC program was compiled or run on hardware.
- **Device and kernel layer.** `mit-plv/bedrock2` at `0005c47b5eaa720bdcb9b94aceaca9f42726b861`,
  `mit-plv/kami` at `9217329eb4e1d751f28ab175ebab230b1e8fd4da`, the Pancake language inside
  `CakeML/cakeml` at `2874b664e10939a3ee462215b2e068c89c1f70eb`, the seL4 device driver framework
  `au-ts/sddf` at `cbbcfe042d8d14d403229e1814769edde333e6bc`, and the seL4 Microkit manual at
  `seL4/microkit` commit `30e1406490d60f446db2a78fd131f3909a62699e`.
- **Prosa.** Release 0.6 (31 October 2025, tested by its authors with Rocq 9.0.0 and mathcomp 2.4.0) as
  described on `https://prosa.mpi-sws.org/`. Prosa's repository is hosted outside GitHub and was not
  reachable from the investigation environment, so no commit hash is recorded and only the project's
  published overview of results was read.
- **Papers** are used for definitions and for the authors' own scope statements; they are cited where used.

The three executed probes are *models* written for this report (plus one harness that executes upstream
C functions verbatim). A passing model run establishes the stated property for that model only.

## Findings

### 1. Superdense tags in the Lingua Franca C runtime

Basis: source + execution.

Representation (`tag/api/tag.h`): `typedef int64_t instant_t; typedef int64_t interval_t;
typedef uint32_t microstep_t; typedef struct { instant_t time; microstep_t microstep; } tag_t;`.
`NEVER` is `LLONG_MIN`, `FOREVER` is `LLONG_MAX`, `FOREVER_MICROSTEP` is `UINT_MAX`,
`NEVER_TAG = (NEVER, 0)`, `FOREVER_TAG = (FOREVER, UINT_MAX)`. Time is nanoseconds.

Order (`lf_tag_compare`): lexicographic, time first.

Arithmetic (`core/tag.c`), stated as equations and confirmed by executing the upstream functions:

| Operation | Result | Note |
|---|---|---|
| `lf_delay_tag((t,m), 0)` | `(t, m+1)` | microstep increment is unsigned and wraps |
| `lf_delay_tag((t,m), d)`, `d > 0` | `(t+d, 0)` | saturates to `FOREVER_TAG` when `t >= FOREVER - d` |
| `lf_delay_tag((t,m), d)`, `d < 0` or `t = NEVER` | `(t, m)` | negative delay is the identity, not an error |
| `lf_delay_strict((t,m), d)`, `d > 0` | `(t+d-1, UINT_MAX)` | the latest tag strictly earlier than `(t+d, 0)` |
| `lf_tag_latest_earlier((t,0))` | `(t-1, UINT_MAX)` | predecessor in the lexicographic order |
| `lf_tag_add((t,m), (s,k))`, `s > 0` | `(t+s, k)` | left microstep is discarded |
| `lf_tag_add((t,m), (0,k))` | `(t, m+k)` | returns `FOREVER_TAG` if `m+k` overflows |

Consequences observed by execution (output reproduced under Evidence):

- Non-additivity: from `g = (100,3)`, `delay(delay(g,0),5) = (105,0)` but `delay(delay(g,5),0) = (105,1)`.
  Positive delays erase microstep history; zero delays accumulate it. Any algebra of "logical delay" over
  these tags is a monoid action only on the sub-domain of strictly positive delays.
- Overflow disagreement: `lf_delay_tag((100, UINT_MAX), 0) = (100, 0)`, which compares *less* than its
  argument, while `lf_tag_add((100, UINT_MAX), (0,1)) = FOREVER_TAG`. The source comments acknowledge
  both ("unsigned variables will wrap on overflow", and a FIXME on the saturating case). A model that
  uses unbounded naturals for microsteps, as the Lean model does, does not represent this.

### 2. Admission of logical and physical actions

Basis: source (`lib/schedule.c`, `lf_schedule_trigger`) + documentation (handbook 0.13.0, "Actions").

The scheduling entry point `lf_schedule_value` enters the environment critical section, calls
`lf_schedule_trigger`, calls `lf_notify_of_event`, and leaves the critical section (the token and copy
variants delegate to internal functions that were not read). In the threaded
runtime the critical section is `lf_mutex_lock(&env->mutex)` and the notification is
`lf_cond_broadcast(&env->event_q_changed)`; in the single-threaded runtime they are
`lf_disable_interrupts_nested()` and a platform hook.

Tag assignment, in source order:

```text
if current_tag is after stop_tag:        reject (warning)
if extra_delay < 0:                      extra_delay := 0 (warning)
delay := extra_delay + (trigger.is_timer ? 0 : trigger.offset)      # offset = declared min_delay
intended := lf_delay_tag(current_tag, delay)                        # logical-action candidate
if trigger.is_physical:
    intended.time      := lf_time_physical() + delay
    intended.time      := max(intended.time, start_tag.time)
    intended.microstep := 0
min_spacing := trigger.period
if min_spacing < 0:                                                 # no spacing declared
    while an event of this trigger already has tag `intended`: intended.microstep++
    (if any bump happened: reject if after stop_tag, else enqueue and return)
else if not timer and trigger.last_tag.time != NEVER:
    earliest := trigger.last_tag.time + min_spacing
    if earliest > intended.time or (earliest == intended.time and min_spacing == 0):
        drop:    discard the new event
        replace: overwrite payload of the still-queued previous event, else behave as defer
        update:  remove the still-queued previous event, keep the new one at `intended`
        defer:   intended := (earliest, 0)                          # default
[debug builds only] if intended.time < current_tag.time: intended.time := current_tag.time
if intended == current_tag: intended.microstep++
reject if intended is after stop_tag
trigger.last_tag := intended; enqueue
```

Points a designer of a logical-time/interrupt bridge should retain:

- **Quantisation rule.** An asynchronous call never produces an event at the current tag: the last rule
  moves an equal tag one microstep later. The tag is advanced inside `_lf_next_locked`, which runs with
  the same mutex held, so stamping and tag advance exclude each other in the threaded runtime.
- **Clamp is a debug-build assertion.** The "event earlier than current time" correction is inside
  `#ifndef NDEBUG`. In a release build the invariant "queued tag >= current tag" for physical actions rests
  on logical time not running ahead of physical time, which is exactly what `fast` mode removes
  (Finding 3). `get_next_event_tag` treats a queue head earlier than the current tag as a fatal error.
- **Back-pressure is a declared policy, not an emergent property.** `defer` never loses events and can
  grow the queue without bound (the handbook says so); `drop` and `replace` bound it and lose events or
  payloads. The handbook (0.13.0) lists three policies and says the policy argument is not supported by
  the C++, TypeScript and Rust targets; the C source at the examined commit has a fourth enumerator,
  `typedef enum { defer, drop, replace, update } lf_spacing_policy_t;`. The handbook's
  `@max_pending_events(<n>)` attribute (default 1; when the limit is reached `defer` "will be handled by
  dropping the event") is introduced there with the words "In micro-LF"; the identifier does not occur in
  the examined `reactor-c` tree, so it does not bound the C runtime's queue.
- **Zero spacing differs from no spacing.** Without a declared spacing, coincident events pile up in
  microsteps; with `min_spacing == 0` the `earliest == intended.time` case is routed through the policy.

### 3. Coupling of logical to physical time, and deadlines

Basis: source (`core/threaded/reactor_threaded.c`) + documentation (handbook 0.13.0, "Deadlines").

`_lf_next_locked` reads the earliest queued tag and calls `wait_until(next_tag.time, &env->event_q_changed)`,
which performs a timed wait on the condition variable (the caller holds the environment mutex, which
the condition wait releases while blocked) and returns
`false` if it was signalled before the timeout. On `false` the loop re-reads the queue head, so a physical
action stamped earlier than the tag being waited for is processed first. `wait_until` skips waiting entirely
when `fast` is set (unless waiting forever under `keepalive`). After the wait the head is read once more
before the tag advances.

The deadline check is `lf_time_physical() > logical_time + deadline`, evaluated when the reaction is about
to run (`lf_check_deadline`). The handbook calls this "lazy" and states the consequence itself: "an LF
program with deadlines becomes nondeterministic. The behavior of the program depends on the exact
timing of the execution." A deadline is a detector with a handler, not a schedulability guarantee.

### 4. Mechanised and model-checked accounts of the reactor model

Basis: source.

Lean model (`ReactorModel/Primitives.lean`): `abbrev Time := Nat`,
`structure Time.Tag where time : Time; microstep : Nat`, with
`le g₁ g₂ := (g₁.time < g₂.time) ∨ (g₁.time = g₂.time ∧ g₁.microstep ≤ g₂.microstep)` and a
`LinearOrder` instance. Results (no `sorry` occurs in the tree):

| Theorem | Statement (as written) | Reading |
|---|---|---|
| `Execution.deterministic` | `(e₁ : Execution s s₁) (e₂ : Execution s s₂) (ht : s₁.tag = s₂.tag) (hp : s₁.progress = s₂.progress) : s₁ = s₂` | executions from one state that stop at the same tag with the same set of completed reactions end in the same state |
| `Execution.tag_le` | `Execution s₁ s₂ → s₁.tag ≤ s₂.tag` | tags never decrease |
| `Execution.not_finitely_variable` | `¬∀ (α) [Proper α] [Reactor.Finite α], FiniteVariability α` | properness and finiteness do not bound the number of steps below a tag; the counterexample reschedules an action at the current time |
| `Execution.weakly_finitely_variable` | `[Hierarchical α] [Reactor.Finite α] : WeakFiniteVariability α` | between two microsteps of one time point the number of steps is bounded (the bound in the proof is `(2·(m − m₀) + 1)·(#rcn + 1) + (#rcn + 1)`) |

`FiniteVariability α` is `∀ g s, ∃ b, ∀ {s'} (e : Execution s s'), s'.tag ≤ g → e.length ≤ b`. The string
"physical" does not occur in the Lean sources: physical actions, deadlines and wall-clock coupling are
outside the model, so its determinism theorem covers the scheduler after tags have been assigned.

Bounded model checking in the compiler (`UclidGenerator.java`) axiomatises tags as integer pairs with
`tag_schedule(t, i) = if (i == 0) then { pi1(t), pi2(t)+1 } else { pi1(t)+i, 0 }` for actions and
`tag_delay(t, i) = if (i == 0) then { pi1(t), pi2(t) } else { pi1(t)+i, 0 }` for connections. The
connection axiom reads the delay as 0 both when no `after` clause is present and when the clause is
zero, and omits the tag constraint altogether for physical connections. The comment in
`CEnclaveGraph.java` says "'after 0' introduce a microstep delay". Whether a property can be affected by
this difference was not tested (see Boundaries).

### 5. Zélus: kinds, causality types, and the discrete cascade

Basis: source; one sentence from the authors' paper is quoted and marked.

Kinds (`compiler/global/deftypes.ml`): `Tstatic of bool | Tany | Tcont | Tdiscrete of bool | Tproba`.
A function type records its kind (`Tfun of kind * ...`), which is what separates combinational,
discrete-time and continuous-time bodies.

Causality types (`compiler/global/defcaus.ml`): a scheme is
`{ typ_vars: t list; typ_rel: (t * t list) list; typ: tc }` with `tc = Cfun of tc * tc | Cproduct of tc list |
Catom of t`. The checker's own header (`compiler/analysis/causality.ml`) states the judgment and its
meaning: "`C | H |-cfree e: ct`" where "causality tags are associated to a strict partial order. The
relation c1 < c2 ... means that e1 must be computed strictly before c2".

Rules that cut instantaneous dependencies, each implemented by typing the argument against a *fresh*
variable unrelated to the result:

| Construct | Source clause | Effect |
|---|---|---|
| `pre e` | `Eunarypre, [e]` | result does not depend on `e` in the instant |
| `e1 fby e2` | `Efby, [e1;e2]` | result depends on `e1`, not on `e2` |
| `up(e)` | `Eup, [e]` (comment: "[up(e)] does not depend instantaneously of itself") | a zero-crossing output does not depend on its argument in the instant |
| `next x = e` | `EQnext` (comment: "[e] does not impose a causality constraint on [n]") | assignment to the next value is non-instantaneous |
| `last x` | `Elast` reads the separate `t_last_typ` of `x` | the left limit has its own causality variable |

Modularity: for every top-level declaration the checker generalises the inferred type
(`let tcs = generalise actual_tc`) and stores it with `Global.set_causality`; the value descriptor has
`value_caus: tc_scheme option` next to the ordinary type scheme and the initialisation scheme, and the
compiler flag `-ic` prints it. A caller is checked against the scheme only. Declaring a function `atomic`
forces "all outputs depend on all inputs" by constraining the whole type below one fresh variable. The
signature is thus a set of strict-order constraints between input and output positions; it reveals the
instantaneous input/output dependency relation and nothing else about the body.

The authors' paper on this analysis (Benveniste, Bourke, Caillaud, Pagano, Pouzet, HSCC 2014) states the
guarantee as: "well typed programs only progress by infinitely small steps outside of zero-crossing
events". Basis for that sentence: documentation (paper); it was not re-derived here.

Runtime cascade (`lib/std/zlsolve.ml`): after a discrete step the loop computes the next horizon and
returns `Goagain true` when `t_horizon <= t`, otherwise `Continue (true, t_horizon)`. `Goagain` keeps
the simulation in the discrete state at the same time (logged as `D.:`); only `Continue` returns to the
solver (logged `D :` then `C :`). A discrete step is entered from the continuous state when
`has_roots || t >= t_horizon`. Several discrete steps can therefore share one real time value: this is
the same superdense structure as an LF microstep sequence, but the index is implicit in the loop rather
than a field of a tag.

### 6. Vélus: verified causality check with atomic node instances

Basis: source.

`src/Lustre/LCausality.v` defines `node_causal n` as: the causality labels of inputs, outputs and locals
are duplicate-free, and there exists an acyclic graph whose vertices are those labels and that has an
edge for every `depends_on_node cx cy n`. The executable check `check_node_causality` builds the graph
and calls `build_acyclic_graph`; `check_node_causality_correct` proves
`check_node_causality n = OK tt -> node_causal n`.

Node application is atomic: the dependency collector has
`| Eapp _ es er a => let ps := PSUnion (collect_used_inst_list er ++ collect_used_inst_list es) in
List.map (fun _ => ps) a`, and the relational definition `IUIapp` says any output `k` of an application
uses `cx` if `cx` is used by any argument or reset expression. Consequently no cross-node causality
interface exists or is needed: an instantaneous feedback path through a node instance is always rejected,
even if the callee's particular output does not depend on that input.

End-to-end statements:

- `behavior_asm` (`src/VelusCorrectness.v`): if elaboration and `lustre_to_asm` succeed, inputs are
  well typed and well clocked, and `Sem.sem_node G main (pStr ins) (pStr outs)` holds, then the assembly
  program has a `Reacts T` behaviour with `bisim_IO G main ins outs T`. Existence of the dataflow
  semantics is a hypothesis here.
- `behavior_asm_exists` and `behavior_asm_new_uniq` (`src/VelusCorrectnessNew.v`) discharge that
  hypothesis from a no-run-time-error condition (`no_rte_global_main`, or the boolean
  `CheckOp.check_global G = true`) and prove uniqueness of the outputs; the uniqueness proof obtains
  causality from `check_causality_correct` and concludes with `det_global`.

The README states that the uninitialised delay `pre` "is not yet treated" (use `0 fby e`), and that the
optional `main_sync` entry point "is not formally verified".

### 7. How the three languages expose causality across module boundaries

Basis: derived from Findings 4 to 6.

| System | Unit of separate checking | What the unit exports about instantaneous dependencies | Cost |
|---|---|---|---|
| Vélus | node | nothing: instances are atomic | rejects feedback through a node even when harmless; no interface to keep stable |
| Zélus | top-level declaration | a causality type scheme: variables per input/output position plus `<` constraints | accepts fine-grained feedback; the dependency relation becomes part of the interface |
| Zélus with `atomic` | declaration | one variable: all outputs after all inputs | same as Vélus, chosen per declaration |
| Lingua Franca | reactor / reaction | reaction declarations and connection delays; `after` with any delay, including zero, moves the effect to a later tag | cycles are broken by a microstep, so "no instantaneous loop" becomes "possibly unbounded microsteps" (Finding 4) |

The minimal signature that preserves static zero-cycle checking without exposing equations is exactly
the Zélus one: the input-to-output instantaneous dependency relation. Anything coarser (Vélus) is sound
and loses programs; anything that replaces rejection by a microstep (Lingua Franca) trades a static
causality error for a liveness question.

### 8. Stack Resource Policy as implemented by RTIC

Basis: source + documentation (the RTIC book in the same repository).

Ceiling analysis (`rtic-macros/src/syntax/analyze.rs`): each shared resource gets an `Ownership` of
`Owned { priority }`, `CoOwned { priority }` (several tasks, equal priority) or
`Contended { ceiling }` with `ceiling: cmp::max(ceiling, priority)` over all accessing tasks. A resource
type is required to be `Send` unless its ceiling is 0, and to be `Sync` when a contended resource is
accessed through a shared reference.

Lock on targets with `BASEPRI` (`rtic/src/export/cortex_basepri.rs`):

```rust
pub unsafe fn lock<T, R>(ptr: *mut T, ceiling: u8, nvic_prio_bits: u8,
                         f: impl FnOnce(&mut T) -> R) -> R {
    unsafe {
        if ceiling == (1 << nvic_prio_bits) {
            critical_section::with(|_| f(&mut *ptr))
        } else {
            let current = basepri::read();
            basepri_max::write(cortex_logical2hw(ceiling, nvic_prio_bits));
            cortex_m::asm::isb();
            let r = f(&mut *ptr);
            asm!("", options(nostack, preserves_flags));
            basepri::write(current);
            r
        }
    }
}
```

with `cortex_logical2hw(logical, bits) = ((1 << bits) - logical) << (8 - bits)`. The `isb` and the empty
`asm!` are there, per the source comments, because "BASEPRI writes are not compiler barriers".

Lock on targets without `BASEPRI` (`cortex_source_mask.rs`; M0, M0+, M23 per its comment): a
compile-time bit mask of interrupts with priority up to the ceiling (`compute_mask(0, ceiling, masks)`;
the doc comment describes the mask as `ceiling >= priority > current`) is cleared in the
interrupt-enable register, followed by `dsb` and `isb`, and restored after the closure; `ceiling >= 4`
falls back to a global critical section. The source lists the limitation: tasks with shared resources
cannot be bound to exception handlers on this back end, "as these cannot be masked in HW".

Mapping to hardware, as the book states it: an interrupt runs when it is pending, enabled, of priority
higher than `BASEPRI`, and highest among such; SRP runs a task when it is requested, of static priority
higher than the system ceiling, and highest among such. `BASEPRI` (or the enable mask) *is* the system
ceiling. The book lists SRP's system-wide requirements as: static priority per task, single core,
run-to-completion tasks, and LIFO resource claims; and states that for async tasks "each section of
code between two yield points ... can be seen as an individual task. The compiler will reject any
attempt to `await` while holding a resource". LIFO order follows from the closure-shaped `lock` API.

Without a user `idle` task, generated `main` ends in the priority-0 dispatcher loop if any priority-0
software task exists, else in `loop {}`; no wait-for-interrupt instruction is emitted by the macro at
this revision, so sleeping is left to user code.

### 9. SRP properties on exhaustive small models

Basis: execution of a model written for this report (source and output under Evidence); normative
reference T. P. Baker, "Stack-based scheduling of realtime processes", Real-Time Systems 3(1), 1991.

The model has one job per task, unit-time operations, and enumerates every combination of release
offsets in a 7-tick window. The SRP rule is the static-priority specialisation: a job may start only if
its priority exceeds both the system ceiling and the priority of the job it would preempt.

| Task set | Protocol | Deadlocked runs | Runs with non-LIFO resumption | Max distinct lower-priority critical sections delaying one job | Max inversion ticks |
|---|---|---|---|---|---|
| two locks taken in opposite order (49 runs) | none | 6 | 9 | 1 | 2 |
| | inheritance | 6 | 9 | 1 | 2 |
| | SRP | 0 | 0 | 1 | 3 |
| high task uses two locks in sequence (343 runs) | none | 0 | 78 | 2 | 7 |
| | inheritance | 0 | 105 | 2 | 6 |
| | SRP | 0 | 0 | 1 | 3 |
| medium task without critical section (343 runs) | none | 0 | 77 | 1 | 6 |
| | inheritance | 0 | 77 | 1 | 2 |
| | SRP | 0 | 0 | 1 | 2 |

Readings:

- Under SRP no run deadlocks, no started job ever finds a lock taken, and a preempted job only resumes
  when it is again the most recently started unfinished job. The last property is what allows one shared
  stack; "non-LIFO resumption" under the other protocols is the event that requires per-task stacks.
- Chained blocking (two distinct critical sections delaying one job) occurs with inheritance and not
  with SRP.
- SRP's price is visible in the first task set: the maximum delay is 3 ticks under SRP against 2 under
  the other protocols (their deadlocked runs are counted only up to the deadlock), because SRP blocks at
  job start for the whole outer
  critical section of any lower job whose ceiling is high enough, whether or not a conflict would occur.

### 10. Wake-up protocols and where lost wake-ups come from

Basis: source + documentation + execution of a model.

Three implementations, one discipline:

- **RTIC async executor** (`rtic/src/export/executor.rs`). A waker runs `set_pending()` then pends the
  dispatcher interrupt. The dispatcher calls
  `poll(wake)`: `if self.is_running() && self.check_and_clear_pending() { ... future.poll(&mut cx) ... }`
  where `check_and_clear_pending` is `compare_exchange(true, false, Acquire, Relaxed)`. The flag is
  cleared *before* the future is polled, so a wake during the poll leaves the flag set and the interrupt
  pending.
- **Shared-queue signalling in the seL4 device driver framework** (`include/sddf/network/queue.h`,
  `network/components/virt_rx.c`; the same shape appears in the Pancake UART driver
  `drivers/serial/imx/uart.pnk`). The consumer drains, calls `net_request_signal_active` (sets
  `consumer_signalled = 0`), then re-tests the queue and, if non-empty, calls `net_cancel_signal_active`
  and repeats. The producer enqueues, then notifies only if `net_require_signal_*` is true, first calling
  `net_cancel_signal_*`.
- **Microkit notifications and interrupts** (manual). Notifications coalesce: "if PD A notifies PD B three
  times on the same channel without PD B ever executing ... it would only see one notification". A
  hardware interrupt "will not be received again until `microkit_irq_ack` is called. The seL4 kernel will
  mask the hardware interrupt until it has been acknowledged". The Pancake UART driver's `notified`
  entry runs `handle_irq()`, a loop that re-reads the status and control registers until no enabled cause
  remains, and only then calls `sddf_deferred_irq_ack(ch)`.
- **Lingua Franca single-threaded sleep on nRF52** (`lf_nrf52_support.c`). The sequence inside the
  critical section is: arm a timer compare, `lf_enable_interrupts_nested(); __WFE();
  lf_disable_interrupts_nested();`, then loop while `!_lf_async_event && (sleep_next ||
  _lf_sleep_interrupted)`. An interrupt service routine that schedules a physical action sets
  `_lf_async_event` through `_lf_single_threaded_notify_of_event`. Correctness of the window between
  enabling interrupts and the wait instruction depends on the processor latching the wake condition;
  that hardware behaviour was not verified here (Boundaries).

Explicit-state exploration of the first two shapes (all interleavings of atomic steps):

| Model | Variant | Outcome |
|---|---|---|
| queue + flag + coalescing notification | upstream order | no terminal state with a non-empty queue and sleeping consumer (1, 2, 3 items) |
| | consumer omits the re-test after arming | lost wake-up, 9-step trace |
| | producer tests the flag before enqueueing | lost wake-up, 11-step trace |
| pending-flag executor | clear before poll | no terminal state with a ready, uncompleted task |
| | poll before clear | lost wake-up, 4-step trace |

The invariant that makes the upstream orders correct is the same in both: *at every point where the
consumer may go to sleep, either the wake condition is false or a notification is latched*. "Arm, then
re-test" establishes it on the consumer side; "publish, then test the arm flag" establishes it on the
producer side. A proof obligation for a device automaton should be phrased as this invariant, not as a
property of either party alone.

The Pancake driver verification paper (Zhao et al., arXiv:2501.08249v2) verifies precisely the producer
half as a functional property of an Ethernet driver: the driver "notifies the OS's semaphores if and only
if (i) a signal was explicitly requested by the OS and (ii) the queue state has been changed by the
driver", and "clears signal requests after notifying the OS (to prevent double signalling)". That is a
safety statement about the driver's calls; the paper's text contains no liveness or lost-wake-up theorem.

### 11. What the mechanised artifacts cover

Basis: source + documentation, per row.

| Artifact | Time and concurrency model in the proof | Interrupts | What is proved | Stated or observed limit |
|---|---|---|---|---|
| Bedrock2 + Kami lightbulb (`end2end_lightbulb`) | single core, I/O trace of memory-mapped reads and writes; `LogItem` is `((mem * string * list word) * (mem * list word))` | none: the trace specification is `BootSeq +++ ((EX b, Recv b +++ LightbulbCmd b) ||| RecvInvalid ||| PollNone) ^*` | every hardware trace is related to a prefix of a good high-level trace | the paper says the design relies "on polling to detect peripheral-initiated flag changes" and that "concurrent software execution (on multiple cores or in interrupt handlers) would require considerable changes to our current approach" |
| Kami (`mit-plv/kami`) | rule-based hardware description | a case-insensitive search for `interrupt`, `mtvec`, `mepc`, `csr` matches one file, and there only six CSR function-code constants | not examined | examined by text search only |
| Pancake (`pancake/` in the CakeML tree) | sequential; device registers accessed by `ShMemLoad` / `ShMemStore`, each evaluated as `call_FFI s.ffi (SharedMem MappedRead \| MappedWrite) ...`, i.e. an observable foreign-call event whose result comes from the oracle | none in the language semantics | `pan_to_target_compile_semantics`: under its installation hypotheses, with `start = «main»` and `semantics_decls s start pan_code ≠ Fail`, `machine_sem mc ffi ms ⊆ extend_with_resource_limit' (...) {semantics_decls s start pan_code}`. Files `pan_itreeSemScript.sml` and `pan_itreeEquivProofScript.sml` exist; their statements were not read | the theorem fixes the entry point to `main`; the driver paper says the same ("to preserve the semantics of the main function") and that extending the proofs "to account for reentry points" is future work; the Pancake-to-Viper transpiler is trusted |
| Pancake Ethernet driver (paper) | event handlers invoked by the kernel; device model written as Viper methods | delivered as notifications; handler is run-to-completion | memory safety and region isolation, device-interface compliance, signalling-protocol compliance, data integrity; about 20 minutes total verification time, of which 10 for the device model | trusts Viper, the SMT solver, the transpiler and the device model |
| Microkit protection domains (manual) | priority-based, budget and period per domain; entry points `init`, `notified`, `protected` | notification on a channel, masked until acknowledged | none (manual) | "A protected call is only possible if the callee has strictly higher priority than the caller"; the call graph must be acyclic; bounded execution of protected procedures is trusted, static enforcement "intended" for a future version |
| Prosa 0.6 (overview of results) | sporadic tasks with arbitrary arrival curves on a uniprocessor; ideal, overhead-afflicted, supply-restricted and resource-model processors | not a modelling concept in the overview | response-time analyses for FIFO, EDF, fixed priority and ELF under four preemption models: fully preemptive, floating non-preemptive sections, segmented limited-preemptive, fully non-preemptive; EDF optimality | the overview lists no analysis parameterised by per-resource ceilings or by a locking protocol |
| RefinedProsa (paper title and abstract) | timed traces of C code linked to Prosa | "interrupt-free schedulers" | response-time bounds for a C scheduler | the abstract contrasts itself with tick-based schedulers; interrupt-driven preemption is outside its stated scope |

The Microkit priority rule for protected procedure calls is the same shape as a ceiling rule: a server
runs at a priority strictly above all its callers, so a client is never preempted by a peer client while
inside the server. This is an observation about the stated rule, not a verified property.

### 12. Design invariants for a bridge between logical time and interrupt-driven code

Basis: derived from Findings 1 to 11. These are consequences, not properties established for any one
system.

1. **Tag after stamping, never before.** An interrupt-originated event must receive a tag strictly greater
   than the tag being executed when it is admitted (Finding 2, last rule). Admission and tag advance
   must exclude each other (mutex or interrupt masking).
2. **State the microstep bound.** A superdense model without a per-time-point bound admits Zeno
   executions (Finding 4) and, in 32-bit microsteps, order inversion on wrap (Finding 1). An interface
   should carry either a strictly positive minimum spacing or an explicit microstep budget.
3. **Bound the admission queue by policy.** `defer` preserves events and needs a proof of bounded arrival
   (a minimum inter-arrival time); `drop`/`replace`/`update` bound memory and need a proof that losing
   an event is acceptable. A response-time analysis with arrival curves (Finding 11, Prosa) is the natural
   supplier of the arrival bound; no examined artifact connects the two.
4. **Ceiling of the admission critical section.** If admission is performed from handlers at several
   priorities, the event queue is a shared resource whose ceiling is the highest such priority; an SRP
   `lock` at that ceiling gives exclusion without a blocking primitive (Finding 8). A global
   interrupt-disable is the degenerate maximal ceiling.
5. **Sleep invariant.** Every path into a wait instruction must establish "condition false or wake latched"
   (Finding 10). For edge-triggered sources this requires acknowledging before the final re-test; for
   level-triggered sources masked until acknowledged, draining to quiescence before acknowledging is
   sufficient.
6. **Causality across the bridge is a delay.** A value that crosses from an interrupt context into a
   synchronous instant must be read through a construct that cuts instantaneous dependency (a tag
   advance in Lingua Franca; `pre`/`fby`/`up` in Zélus; any registered input in Vélus), otherwise the
   static causality check of the synchronous side says nothing about it.
7. **Deadlines are observations.** A lag check that runs when the reaction starts (Finding 3) cannot bound
   the reaction's own execution time. A guarantee needs a schedulability argument outside the language.

## Boundaries

- **not examined** — The ChucK and Filament languages; Lingua Franca's federated execution (safe-to-advance
  offsets, the runtime infrastructure) and its non-C runtimes; RTIC's RISC-V back ends, `rtic-sync`
  channels and `rtic-monotonics`; the Zélus manual and its ODE solver interfaces; Kami beyond a text
  search for interrupt and CSR terms; Prosa's Rocq sources (only the published overview and release
  page were readable); the full text of Baker's 1991 article (behind a paywall in this environment; its
  results are represented here by the RTIC book's summary, the indexing abstract "sharing of runtime
  stack space between jobs ... dynamic priority schemes ... that use static 'preemption levels'", and the
  model run).
- **not examined** — Processor semantics of wait-for-event and wait-for-interrupt instructions, interrupt
  pending latches, and `BASEPRI` side effects were not checked against the architecture manuals. Claims
  in Findings 8 and 10 about hardware are restricted to what the cited source comments and book say.
- **not examined** — No Lingua Franca, Zélus, Vélus, RTIC, Bedrock2 or Pancake program was compiled,
  and no proof development was rebuilt. Theorem statements are quoted from source; their proofs were
  not replayed.
- **unknown** — Whether the difference between the bounded-model-checking axiom for zero-delay
  connections and the runtime's microstep increment (Finding 4) can make the verifier accept a property
  the runtime violates. Only the generator was read.
- **unknown** — Whether a mechanised proof of the SRP theorems, or of RTIC's code generation against
  them, exists. None was found in the examined repositories; the absence is not evidence of
  non-existence elsewhere.
- **unknown** — Whether the `update` spacing policy present in the C source is documented in a handbook
  version later than the one read (0.13.0), and how the micro-LF runtime enforces
  `@max_pending_events`.
- **known not to apply** — The Bedrock2/Kami end-to-end theorem does not cover interrupt-driven
  software; its trace specification contains only polling. The Lean reactor model's determinism theorem
  does not cover physical actions or deadlines. Vélus accepts no instantaneous feedback through a node
  instance. Prosa's listed analyses bound response times given a preemption model; they do not derive
  that model from a locking protocol.
- **unsupported** — RTIC's source-masking back end cannot protect resources shared with tasks bound to
  processor exceptions. Vélus does not treat uninitialised `pre`. The Lingua Franca handbook states the
  spacing policy argument is not supported by the C++, TypeScript and Rust targets.
- **Stronger conclusions not established.** The model runs in Findings 9 and 10 do not show that RTIC,
  the driver framework or the Lingua Franca runtime are free of deadlock or lost wake-ups; they show
  that the protocol shapes read from those sources have the property in small abstract models and that
  nearby variants do not. Nothing here shows that composing superdense logical time with SRP-scheduled
  interrupt handlers has been verified by anyone.

## Evidence

All repository evidence was read on 2026-11-19 from snapshots of the stated commits. Line numbers refer
to those commits.

### Source locations

| Repository @ commit | Path | Lines / symbol | Used for |
|---|---|---|---|
| `lf-lang/reactor-c` @ `abbf0aaf468af55f298e1ae4816156e9f7552784` | `tag/api/tag.h` | 55–76, 100–122 | constants, `instant_t`, `microstep_t`, `tag_t` |
| | `core/tag.c` | 86–177 | `lf_tag_add`, `lf_tag_compare`, `lf_delay_tag`, `lf_delay_strict`, `lf_tag_latest_earlier` |
| | `lib/schedule.c` | 46–70, 82–92, 102–345 | `lf_schedule_value`, `lf_check_deadline`, `lf_schedule_trigger` |
| | `include/core/lf_types.h` | 105 | `lf_spacing_policy_t` |
| | `core/threaded/reactor_threaded.c` | 181–211, 254–420, 1694–1705 | `wait_until`, `_lf_next_locked`, notify and critical section |
| | `core/reactor.c` | 438–451 | single-threaded notify and critical section |
| | `low_level_platform/impl/src/lf_nrf52_support.c` | 184–243, 290–293 | interruptible sleep, async-event flag |
| `lf-lang/lingua-franca` @ `0df8a987e37d6bc0cc8daa1c3e6167df14eaae59` | `core/src/main/java/org/lflang/LinguaFranca.xtext` | 158–172 | action grammar and its comment |
| | `core/src/main/java/org/lflang/analyses/uclid/UclidGenerator.java` | 381–386, 872–932, 975–1000 | tag axioms, connection and action axioms |
| | `core/src/main/java/org/lflang/generator/c/CEnclaveGraph.java` | 140 | comment on `after 0` |
| `marcusrossel/reactor-model` @ `7a7d1f36ba5b908f2d3744f8cd08186eac325fe6` | `ReactorModel/Primitives.lean` | 50–64 | `Time.Tag` and its order |
| | `ReactorModel/Execution/Theorems/Execution.lean` | 14–23 | `deterministic`, `tag_le` |
| | `ReactorModel/Execution/Theorems/Variability/Basic.lean`, `Weak.lean` | 21–34; 18–24 | variability definitions and theorems |
| `INRIA/zelus` @ `5f6e4903103e136f52cdcefc13a9bdcff0f53abd` | `compiler/global/defcaus.ml` | 19–51 | causality types |
| | `compiler/analysis/causality.ml` | 17–27, 294–301, 374–392, 477–481, 719–739 | judgment header, `last`, operators, `next`, declaration handling |
| | `compiler/global/global.ml`, `compiler/main/zeluc.ml` | 28–31; 127–129 | `value_caus`, `-ic` |
| | `lib/std/zlsolve.ml` | 336–351, 455–520 | discrete cascade, state transitions |
| `INRIA/velus` @ `27ba860c2624ba232816591290c6c119b9ead88a` | `src/Lustre/LCausality.v` | 68–72, 580–587, 812–814, 934–943, 2296–2300 | `IUIapp`, `node_causal`, collector, checker and its correctness |
| | `src/VelusCorrectness.v`, `src/VelusCorrectnessNew.v` | 202–210; 507–581 | end-to-end theorems |
| | `README.md` | opening section | `pre`, `main_sync` |
| `rtic-rs/rtic` @ `fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9` | `rtic/src/export/cortex_basepri.rs` | 27–81 | BASEPRI `lock` |
| | `rtic/src/export/cortex_source_mask.rs` | 9–16, 77–158 | mask-based `lock`, limitation |
| | `rtic/src/export/cortex_common.rs` | 5–7 | `cortex_logical2hw` |
| | `rtic/src/export/executor.rs` | 205–292 | `AsyncTaskExecutor` |
| | `rtic-macros/src/syntax/analyze.rs` | 202–292, 388–406 | ownership and ceilings |
| | `rtic-macros/src/codegen/main.rs`, `async_dispatchers.rs` | 17–25; 23–91 | idle fallback, dispatchers |
| | `book/en/src/preface.md` | 43–146 | SRP summary and hardware mapping |
| `mit-plv/bedrock2` @ `0005c47b5eaa720bdcb9b94aceaca9f42726b861` | `bedrock2/src/bedrock2/Semantics.v` | 12–25 | `LogItem`, `trace`, `ExtSpec` |
| | `bedrock2/src/bedrock2Examples/lightbulb_spec.v` | 204–227 | `goodHlTrace` |
| | `end2end/src/end2end/End2EndLightbulb.v` | 167–175 | `end2end_lightbulb` |
| `mit-plv/kami` @ `9217329eb4e1d751f28ab175ebab230b1e8fd4da` | `Kami/Ex/IsaRv32.v` | 241–246 | only CSR function codes match an interrupt/CSR search |
| `CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb` | `pancake/panLangScript.sml` | 76–97 | `prog` constructors |
| | `pancake/proofs/pan_to_targetProofScript.sml` | 1285–1326 | `pan_to_target_compile_semantics` |
| | `pancake/semantics/panSemScript.sml` | 511–545, 605–615, 717–725 | shared-memory and foreign-call evaluation |
| `au-ts/sddf` @ `cbbcfe042d8d14d403229e1814769edde333e6bc` | `include/sddf/network/queue.h` | 263–328 | signalling flag operations |
| | `network/components/virt_rx.c` | 60–131 | drain / arm / re-test loop |
| | `drivers/serial/imx/uart.pnk` | 152–262 | Pancake driver handlers |
| `seL4/microkit` @ `30e1406490d60f446db2a78fd131f3909a62699e` | `docs/manual.md` | 296–358, 776–797 | protected procedures, notifications, interrupts |

### Documents

- Lingua Franca handbook, version label 0.13.0, pages "Superdense Time", "Actions", "Deadlines" under
  `https://www.lf-lang.org/docs/writing-reactors/`.
- Prosa: `https://prosa.mpi-sws.org/results/` (overview of verified results) and
  `https://prosa.mpi-sws.org/get-prosa/` (release 0.6, 31 October 2025).
- T. P. Baker, "Stack-based scheduling of realtime processes", Real-Time Systems 3(1):67–99, 1991,
  doi:10.1007/BF00365393 (bibliographic record and indexing abstract only).
- M. Lohstroh, C. Menard, S. Bateni, E. A. Lee, "Toward a Lingua Franca for Deterministic Concurrent
  Systems", ACM TECS 20(4), 2021, doi:10.1145/3448128 (bibliographic record).
- M. Rossel, S. Lin, M. Lohstroh, J. Castrillón, A. Goens, "Provable Determinism for Software in
  Cyber-Physical Systems", VSTTE 2023 (named by the reactor-model README as its description).
- T. Bourke, M. Pouzet, "Zélus: A Synchronous Language with ODEs", HSCC 2013,
  doi:10.1145/2461328.2461348; A. Benveniste, T. Bourke, B. Caillaud, B. Pagano, M. Pouzet, "A Type-based
  Analysis of Causality Loops in Hybrid Systems Modelers", HSCC 2014 (abstract sentence quoted in
  Finding 5).
- A. Erbsen, S. Gruetter, J. Choi, C. Wood, A. Chlipala, "Integration Verification across Software and
  Hardware for a Simple Embedded System", PLDI 2021, doi:10.1145/3453483.3454065 (full text read;
  quotations in Finding 11).
- J. Zhao et al., "Verifying Device Drivers with Pancake", arXiv:2501.08249v2 (full text read; quotations
  in Findings 10 and 11).
- K. Bedarkar, L. Elbeheiry, M. Sammler, L. Gäher, B. Brandenburg, D. Dreyer, D. Garg, "RefinedProsa:
  Connecting Response-Time Analysis with C Verification for Interrupt-Free Schedulers", PLDI 2025
  (title and abstract).

### Probe A: upstream tag arithmetic

Environment: Linux x86_64, `gcc (Debian 15.2.0-14) 15.2.0`. The harness includes, verbatim, the pure
functions of `core/tag.c` from `lf_time_add` up to (not including) `lf_time_logical`.

```sh
SHA=abbf0aaf468af55f298e1ae4816156e9f7552784
mkdir -p /tmp/tagprobe && cd /tmp/tagprobe
curl -sSLO https://raw.githubusercontent.com/lf-lang/reactor-c/$SHA/tag/api/tag.h
curl -sSL -o tag_full.c https://raw.githubusercontent.com/lf-lang/reactor-c/$SHA/core/tag.c
s=$(grep -n '^instant_t lf_time_add' tag_full.c | cut -d: -f1)
e=$(grep -n '^instant_t lf_time_logical' tag_full.c | cut -d: -f1)
sed -n "${s},$((e-1))p" tag_full.c > tag_pure_extract.inc
# save the C block below as tag_probe.c, then:
gcc -std=c11 -Wall -Wextra -O1 -I . -o tag_probe tag_probe.c && ./tag_probe
```

```c
// Probe: exercise the pure tag-arithmetic functions of lf-lang/reactor-c
// (core/tag.c, extracted verbatim into tag_pure_extract.inc) against tag/api/tag.h.
#include <stdio.h>
#include <limits.h>
#include "tag.h"
#include "tag_pure_extract.inc"

static void show(const char* label, tag_t g) {
  if (g.time == FOREVER) printf("%-46s = (FOREVER, %u)\n", label, g.microstep);
  else if (g.time == NEVER) printf("%-46s = (NEVER, %u)\n", label, g.microstep);
  else printf("%-46s = (%lld, %u)\n", label, (long long)g.time, g.microstep);
}

int main(void) {
  tag_t g = {.time = 100, .microstep = 3};
  show("g", g);
  show("lf_delay_tag(g, 0)", lf_delay_tag(g, 0));
  show("lf_delay_tag(g, 5)", lf_delay_tag(g, 5));
  show("lf_delay_tag(g, -1)   [negative: identity]", lf_delay_tag(g, -1));
  // Non-additivity: delaying by 0 then d differs from delaying by d then 0.
  show("lf_delay_tag(lf_delay_tag(g,0),5)", lf_delay_tag(lf_delay_tag(g, 0), 5));
  show("lf_delay_tag(lf_delay_tag(g,5),0)", lf_delay_tag(lf_delay_tag(g, 5), 0));
  // Two zero delays accumulate microsteps; two positive delays do not.
  show("lf_delay_tag(lf_delay_tag(g,0),0)", lf_delay_tag(lf_delay_tag(g, 0), 0));
  show("lf_delay_tag(lf_delay_tag(g,2),3)", lf_delay_tag(lf_delay_tag(g, 2), 3));
  // Strict delay: latest tag strictly earlier than (t+d, 0).
  show("lf_delay_strict(g, 5)", lf_delay_strict(g, 5));
  show("lf_delay_strict(g, 0)", lf_delay_strict(g, 0));
  show("lf_tag_latest_earlier((100,0))", lf_tag_latest_earlier((tag_t){100, 0}));
  show("lf_tag_latest_earlier((100,3))", lf_tag_latest_earlier(g));
  // lf_tag_add resets the left microstep when the right time is positive.
  show("lf_tag_add((100,3),(0,2))", lf_tag_add(g, (tag_t){0, 2}));
  show("lf_tag_add((100,3),(5,2))", lf_tag_add(g, (tag_t){5, 2}));
  // Microstep overflow behaviour differs between the two functions.
  tag_t top = {.time = 100, .microstep = UINT_MAX};
  show("lf_delay_tag((100,UINT_MAX),0)  [wraps]", lf_delay_tag(top, 0));
  show("lf_tag_add((100,UINT_MAX),(0,1)) [saturates]", lf_tag_add(top, (tag_t){0, 1}));
  printf("compare((100,UINT_MAX),(100,0)) after wrap     = %d\n",
         lf_tag_compare(lf_delay_tag(top, 0), top));
  // Time overflow saturates to FOREVER_TAG.
  show("lf_delay_tag((FOREVER-1,0),1)", lf_delay_tag((tag_t){FOREVER - 1, 0}, 1));
  // Lexicographic order.
  printf("compare((100,3),(100,4)) = %d, compare((100,9),(101,0)) = %d, compare(g,g) = %d\n",
         lf_tag_compare(g, (tag_t){100, 4}), lf_tag_compare((tag_t){100, 9}, (tag_t){101, 0}),
         lf_tag_compare(g, g));
  printf("sizeof(instant_t)=%zu sizeof(microstep_t)=%zu\n", sizeof(instant_t), sizeof(microstep_t));
  return 0;
}
```

Output:

```text
g                                              = (100, 3)
lf_delay_tag(g, 0)                             = (100, 4)
lf_delay_tag(g, 5)                             = (105, 0)
lf_delay_tag(g, -1)   [negative: identity]     = (100, 3)
lf_delay_tag(lf_delay_tag(g,0),5)              = (105, 0)
lf_delay_tag(lf_delay_tag(g,5),0)              = (105, 1)
lf_delay_tag(lf_delay_tag(g,0),0)              = (100, 5)
lf_delay_tag(lf_delay_tag(g,2),3)              = (105, 0)
lf_delay_strict(g, 5)                          = (104, 4294967295)
lf_delay_strict(g, 0)                          = (100, 4)
lf_tag_latest_earlier((100,0))                 = (99, 4294967295)
lf_tag_latest_earlier((100,3))                 = (100, 2)
lf_tag_add((100,3),(0,2))                      = (100, 5)
lf_tag_add((100,3),(5,2))                      = (105, 2)
lf_delay_tag((100,UINT_MAX),0)  [wraps]        = (100, 0)
lf_tag_add((100,UINT_MAX),(0,1)) [saturates]   = (FOREVER, 4294967295)
compare((100,UINT_MAX),(100,0)) after wrap     = -1
lf_delay_tag((FOREVER-1,0),1)                  = (FOREVER, 4294967295)
compare((100,3),(100,4)) = -1, compare((100,9),(101,0)) = -1, compare(g,g) = 0
sizeof(instant_t)=8 sizeof(microstep_t)=4
```

### Probe B: resource protocols on small models

Environment: Python 3.13.15, standard library only. Run `python3 srp_probe.py`; exit status 0.

```python
#!/usr/bin/env python3
"""Exhaustive small-model comparison of three uniprocessor resource protocols.

Protocols:
  NONE  plain mutexes, fixed-priority preemptive scheduling, no priority adjustment
  PIP   priority inheritance (holder inherits the priority of jobs it blocks)
  SRP   Baker's Stack Resource Policy specialised to static priorities
        (= immediate ceiling): a job may START only if its priority is strictly
        greater than the system ceiling (max ceiling of all held resources) and
        than the priority of the job it would preempt.

Each task releases exactly one job; a job is a list of unit-time ops:
  ("lock", R) | ("unlock", R) | ("work",)
All release-offset combinations in a bounded window are enumerated.
Only the Python standard library is used.
"""
import itertools
import sys

TASKSETS = {
    # Opposite nesting order: the classic two-lock deadlock shape.
    "opposite-nesting": {
        "A": (1, [("lock", "R1"), ("lock", "R2"), ("unlock", "R2"), ("unlock", "R1")]),
        "B": (2, [("lock", "R2"), ("lock", "R1"), ("unlock", "R1"), ("unlock", "R2")]),
    },
    # H uses R1 then R2 sequentially; L holds R1, M holds R2: chained blocking shape.
    "chained-blocking": {
        "L": (1, [("lock", "R1"), ("work",), ("work",), ("unlock", "R1")]),
        "M": (2, [("lock", "R2"), ("work",), ("work",), ("unlock", "R2")]),
        "H": (3, [("lock", "R1"), ("unlock", "R1"), ("lock", "R2"), ("unlock", "R2")]),
    },
    # A medium job without any critical section: unbounded-inversion shape.
    "medium-interference": {
        "L": (1, [("lock", "R1"), ("work",), ("unlock", "R1")]),
        "M": (2, [("work",), ("work",), ("work",), ("work",)]),
        "H": (3, [("work",), ("lock", "R1"), ("unlock", "R1")]),
    },
}
WINDOW = 7  # release offsets 0..WINDOW-1


def ceilings(tasks):
    c = {}
    for _name, (prio, ops) in tasks.items():
        for op in ops:
            if op[0] == "lock":
                c[op[1]] = max(c.get(op[1], 0), prio)
    return c


def simulate(tasks, releases, protocol):
    ceil = ceilings(tasks)
    prio = {n: tasks[n][0] for n in tasks}
    ops = {n: tasks[n][1] for n in tasks}
    pc = {n: 0 for n in tasks}
    holder = {}           # resource -> job
    held = {n: [] for n in tasks}
    started = []          # stack of started, unfinished jobs (start order)
    finished = set()
    cs_id = {n: 0 for n in tasks}      # outermost critical-section counter
    blocking_cs = {n: set() for n in tasks}
    inversion_ticks = {n: 0 for n in tasks}
    res = {"deadlock": False, "stack_violation": 0, "lock_blocked_after_start": 0,
           "mutex_violation": 0}
    t = 0
    horizon = WINDOW + sum(len(o) for o in ops.values()) + 5
    while len(finished) < len(tasks) and t < horizon:
        pending = [n for n in tasks if releases[n] <= t and n not in finished]
        if not pending:
            t += 1
            continue

        def blocked(n):
            op = ops[n][pc[n]]
            return op[0] == "lock" and op[1] in holder and holder[op[1]] != n

        if protocol == "SRP":
            sys_ceiling = max([ceil[r] for r in holder], default=0)
            top = started[-1] if started else None
            floor = max(sys_ceiling, prio[top] if top else 0)
            fresh = [n for n in pending if n not in started and prio[n] > floor]
            run = max(fresh, key=lambda n: prio[n]) if fresh else top
            if run is None:
                # nothing started and nothing may start: impossible when no resource is held
                res["deadlock"] = True
                break
            if blocked(run):
                res["lock_blocked_after_start"] += 1
                res["deadlock"] = True
                break
        else:
            eff = dict(prio)
            if protocol == "PIP":
                changed = True
                while changed:
                    changed = False
                    for n in pending:
                        if blocked(n):
                            h = holder[ops[n][pc[n]][1]]
                            if eff[h] < eff[n]:
                                eff[h] = eff[n]
                                changed = True
            runnable = [n for n in pending if not blocked(n)]
            if not runnable:
                res["deadlock"] = True
                break
            run = max(runnable, key=lambda n: (eff[n], prio[n]))

        # stack discipline: the running job is the top of the start stack or is pushed now
        if run not in started:
            started.append(run)
        elif started[-1] != run:
            res["stack_violation"] += 1

        # accounting: which pending higher-priority jobs are delayed by `run`?
        for n in pending:
            if n != run and prio[n] > prio[run]:
                inversion_ticks[n] += 1
                if held[run] or ops[run][pc[run]][0] == "lock":
                    blocking_cs[n].add((run, cs_id[run]))

        op = ops[run][pc[run]]
        if op[0] == "lock":
            if op[1] in holder:
                res["mutex_violation"] += 1
            holder[op[1]] = run
            held[run].append(op[1])
        elif op[0] == "unlock":
            del holder[op[1]]
            held[run].remove(op[1])
            if not held[run]:
                cs_id[run] += 1
        pc[run] += 1
        if pc[run] == len(ops[run]):
            finished.add(run)
            started.remove(run)
        t += 1
    res["max_blocking_cs"] = max(len(s) for s in blocking_cs.values())
    res["max_inversion_ticks"] = max(inversion_ticks.values())
    return res


def main():
    ok = True
    for name, tasks in TASKSETS.items():
        print(f"taskset {name}: ceilings={ceilings(tasks)}")
        names = sorted(tasks)
        for protocol in ("NONE", "PIP", "SRP"):
            agg = {"runs": 0, "deadlock": 0, "stack_violation": 0, "mutex_violation": 0,
                   "lock_blocked_after_start": 0, "max_blocking_cs": 0, "max_inversion_ticks": 0}
            for offs in itertools.product(range(WINDOW), repeat=len(names)):
                r = simulate(tasks, dict(zip(names, offs)), protocol)
                agg["runs"] += 1
                agg["deadlock"] += int(r["deadlock"])
                agg["stack_violation"] += int(r["stack_violation"] > 0)
                agg["mutex_violation"] += r["mutex_violation"]
                agg["lock_blocked_after_start"] += r["lock_blocked_after_start"]
                agg["max_blocking_cs"] = max(agg["max_blocking_cs"], r["max_blocking_cs"])
                agg["max_inversion_ticks"] = max(agg["max_inversion_ticks"], r["max_inversion_ticks"])
            print(f"  {protocol:4s} runs={agg['runs']:4d} deadlocked_runs={agg['deadlock']:3d} "
                  f"runs_with_non_LIFO_resume={agg['stack_violation']:3d} "
                  f"max_distinct_blocking_critical_sections={agg['max_blocking_cs']} "
                  f"max_priority_inversion_ticks={agg['max_inversion_ticks']} "
                  f"mutex_violations={agg['mutex_violation']}")
            if protocol == "SRP":
                ok &= (agg["deadlock"] == 0 and agg["stack_violation"] == 0
                       and agg["max_blocking_cs"] <= 1 and agg["mutex_violation"] == 0
                       and agg["lock_blocked_after_start"] == 0)
    print("SRP_INVARIANTS_HOLD" if ok else "SRP_INVARIANT_VIOLATED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
```

Output:

```text
taskset opposite-nesting: ceilings={'R1': 2, 'R2': 2}
  NONE runs=  49 deadlocked_runs=  6 runs_with_non_LIFO_resume=  9 max_distinct_blocking_critical_sections=1 max_priority_inversion_ticks=2 mutex_violations=0
  PIP  runs=  49 deadlocked_runs=  6 runs_with_non_LIFO_resume=  9 max_distinct_blocking_critical_sections=1 max_priority_inversion_ticks=2 mutex_violations=0
  SRP  runs=  49 deadlocked_runs=  0 runs_with_non_LIFO_resume=  0 max_distinct_blocking_critical_sections=1 max_priority_inversion_ticks=3 mutex_violations=0
taskset chained-blocking: ceilings={'R1': 3, 'R2': 3}
  NONE runs= 343 deadlocked_runs=  0 runs_with_non_LIFO_resume= 78 max_distinct_blocking_critical_sections=2 max_priority_inversion_ticks=7 mutex_violations=0
  PIP  runs= 343 deadlocked_runs=  0 runs_with_non_LIFO_resume=105 max_distinct_blocking_critical_sections=2 max_priority_inversion_ticks=6 mutex_violations=0
  SRP  runs= 343 deadlocked_runs=  0 runs_with_non_LIFO_resume=  0 max_distinct_blocking_critical_sections=1 max_priority_inversion_ticks=3 mutex_violations=0
taskset medium-interference: ceilings={'R1': 3}
  NONE runs= 343 deadlocked_runs=  0 runs_with_non_LIFO_resume= 77 max_distinct_blocking_critical_sections=1 max_priority_inversion_ticks=6 mutex_violations=0
  PIP  runs= 343 deadlocked_runs=  0 runs_with_non_LIFO_resume= 77 max_distinct_blocking_critical_sections=1 max_priority_inversion_ticks=2 mutex_violations=0
  SRP  runs= 343 deadlocked_runs=  0 runs_with_non_LIFO_resume=  0 max_distinct_blocking_critical_sections=1 max_priority_inversion_ticks=2 mutex_violations=0
SRP_INVARIANTS_HOLD
```

### Probe C: wake-up protocols

Environment: Python 3.13.15, standard library only. Run `python3 wakeup_probe.py`; exit status 0.

```python
#!/usr/bin/env python3
"""Explicit-state exploration of two wake-up protocols (Python standard library only).

Model A: single-producer/single-consumer shared queue with a "consumer needs signal"
flag and a coalescing (binary) notification, in the shape used by event-driven
driver frameworks on a microkernel:

  consumer handler (runs once per delivered notification):
      loop:  drain queue
             flag := NEED_SIGNAL
             if queue non-empty: flag := NO_SIGNAL; repeat      # the re-check
             else: return (wait for next notification)
  producer:  enqueue; if flag == NEED_SIGNAL: flag := NO_SIGNAL; notify

Variants: correct, no-recheck (consumer returns right after setting the flag),
and check-before-enqueue (producer tests the flag before enqueueing).

Model B: a pending-flag task executor in the shape used by interrupt-dispatched
async executors:

  waker:      pending := true              (then pend the dispatcher interrupt)
  dispatcher: if test-and-clear(pending): poll()      # clear BEFORE poll
  poll():     if ready: complete

Variants: clear-before-poll (correct) and poll-before-clear.

The checked property in both models: no terminal state has undelivered work
(a non-empty queue with a sleeping consumer / a ready-but-never-completed task).
Every step of each process is atomic; all interleavings are explored (BFS).
"""
from collections import deque
import sys


def explore(init, step, bad_terminal):
    seen = {init: None}
    todo = deque([init])
    terminals = 0
    while todo:
        s = todo.popleft()
        succ = step(s)
        if not succ:
            terminals += 1
            if bad_terminal(s):
                path = []
                cur = s
                while cur is not None:
                    prev = seen[cur]
                    path.append(cur if prev is None else (prev[1], cur))
                    cur = None if prev is None else prev[0]
                path.reverse()
                return len(seen), terminals, path
        for label, t in succ:
            if t not in seen:
                seen[t] = (s, label)
                todo.append(t)
    return len(seen), terminals, None


# ----------------------------- Model A ------------------------------------
NEED, NOSIG = 0, 1


def model_a(variant, items):
    # state: (q, flag, notif, cpc, ppc, left)
    init = (0, NEED, 0, "wait", "enq" if variant != "check-before-enqueue" else "chk", items)

    def step(s):
        q, flag, notif, cpc, ppc, left = s
        out = []
        # consumer
        if cpc == "wait":
            if notif:
                out.append(("C:take-notification", (q, flag, 0, "drain", ppc, left)))
        elif cpc == "drain":
            if q > 0:
                out.append(("C:dequeue", (q - 1, flag, notif, "drain", ppc, left)))
            else:
                out.append(("C:queue-empty", (q, flag, notif, "request", ppc, left)))
        elif cpc == "request":
            nxt = "wait" if variant == "no-recheck" else "recheck"
            out.append(("C:flag:=NEED", (q, NEED, notif, nxt, ppc, left)))
        elif cpc == "recheck":
            if q > 0:
                out.append(("C:recheck-nonempty;flag:=NOSIG", (q, NOSIG, notif, "drain", ppc, left)))
            else:
                out.append(("C:recheck-empty;return", (q, flag, notif, "wait", ppc, left)))
        # producer
        if variant == "check-before-enqueue":
            if ppc == "chk" and left > 0:
                out.append(("P:test-flag", (q, flag, notif, cpc, "enq+" if flag == NEED else "enq-", left)))
            elif ppc == "enq+":
                out.append(("P:enqueue", (q + 1, flag, notif, cpc, "cancel", left - 1)))
            elif ppc == "enq-":
                out.append(("P:enqueue(no-signal)", (q + 1, flag, notif, cpc, "chk", left - 1)))
            elif ppc == "cancel":
                out.append(("P:flag:=NOSIG", (q, NOSIG, notif, cpc, "notify", left)))
            elif ppc == "notify":
                out.append(("P:notify", (q, flag, 1, cpc, "chk", left)))
        else:
            if ppc == "enq" and left > 0:
                out.append(("P:enqueue", (q + 1, flag, notif, cpc, "test", left - 1)))
            elif ppc == "test":
                if flag == NEED:
                    out.append(("P:flag==NEED;flag:=NOSIG", (q, NOSIG, notif, cpc, "notify", left)))
                else:
                    out.append(("P:flag==NOSIG;skip", (q, flag, notif, cpc, "enq", left)))
            elif ppc == "notify":
                out.append(("P:notify", (q, flag, 1, cpc, "enq", left)))
        return out

    def bad(s):
        q, _flag, notif, cpc, _ppc, _left = s
        return q > 0 and cpc == "wait" and not notif

    return init, step, bad


# ----------------------------- Model B ------------------------------------
def model_b(variant):
    # state: (ready, pending, done, dpc, epc)
    init = (False, True, False, "idle", "set")     # task spawned: pending initially set

    def step(s):
        ready, pending, done, dpc, epc = s
        out = []
        if not done:
            if variant == "clear-before-poll":
                if dpc == "idle" and pending:
                    out.append(("D:test-and-clear", (ready, False, done, "poll", epc)))
                elif dpc == "poll":
                    out.append(("D:poll", (ready, pending, ready, "idle", epc)))
            else:
                if dpc == "idle" and pending:
                    out.append(("D:poll", (ready, pending, ready, "clear", epc)))
                elif dpc == "clear":
                    out.append(("D:clear", (ready, False, done, "idle", epc)))
        if epc == "set":
            out.append(("E:ready:=true", (True, pending, done, dpc, "wake")))
        elif epc == "wake":
            out.append(("E:wake(pending:=true)", (ready, True, done, dpc, "end")))
        return out

    def bad(s):
        ready, _pending, done, _dpc, _epc = s
        return ready and not done

    return init, step, bad


def report(name, res):
    states, terminals, path = res
    if path is None:
        print(f"{name}: states={states} terminal_states={terminals} lost_wakeup=NONE")
        return True
    print(f"{name}: states={states} lost_wakeup=REACHABLE, shortest trace ({len(path) - 1} steps):")
    print("    " + " ; ".join(p[0] for p in path[1:]))
    return False


def main():
    ok = True
    for items in (1, 2, 3):
        ok &= report(f"A/correct items={items}", explore(*model_a("correct", items)))
    bad1 = report("A/no-recheck items=2", explore(*model_a("no-recheck", 2)))
    bad2 = report("A/check-before-enqueue items=2", explore(*model_a("check-before-enqueue", 2)))
    ok &= report("B/clear-before-poll", explore(*model_b("clear-before-poll")))
    bad3 = report("B/poll-before-clear", explore(*model_b("poll-before-clear")))
    expected = ok and not bad1 and not bad2 and not bad3
    print("EXPECTED_OUTCOME" if expected else "UNEXPECTED_OUTCOME")
    return 0 if expected else 1


if __name__ == "__main__":
    sys.exit(main())
```

Output:

```text
A/correct items=1: states=9 terminal_states=1 lost_wakeup=NONE
A/correct items=2: states=48 terminal_states=1 lost_wakeup=NONE
A/correct items=3: states=132 terminal_states=1 lost_wakeup=NONE
A/no-recheck items=2: states=25 lost_wakeup=REACHABLE, shortest trace (9 steps):
    P:enqueue ; P:flag==NEED;flag:=NOSIG ; P:notify ; C:take-notification ; C:dequeue ; C:queue-empty ; P:enqueue ; P:flag==NOSIG;skip ; C:flag:=NEED
A/check-before-enqueue items=2: states=35 lost_wakeup=REACHABLE, shortest trace (11 steps):
    P:test-flag ; P:enqueue ; P:flag:=NOSIG ; P:notify ; C:take-notification ; C:dequeue ; C:queue-empty ; P:test-flag ; C:flag:=NEED ; C:recheck-empty;return ; P:enqueue(no-signal)
B/clear-before-poll: states=12 terminal_states=2 lost_wakeup=NONE
B/poll-before-clear: states=11 lost_wakeup=REACHABLE, shortest trace (4 steps):
    D:poll ; E:ready:=true ; E:wake(pending:=true) ; D:clear
EXPECTED_OUTCOME
```

## Revalidation

- **Tag arithmetic.** Re-run Probe A against another `reactor-c` commit by changing `SHA`. Any change in
  the output lines identifies a change in `lf_delay_tag`, `lf_delay_strict`, `lf_tag_add`,
  `lf_tag_latest_earlier` or `lf_tag_compare`. If the extraction anchors (`lf_time_add`,
  `lf_time_logical`) no longer exist, the file was restructured and Finding 1 must be re-read from source.
- **Admission algorithm.** Diff `lib/schedule.c` between the pinned commit and the commit of interest,
  restricted to `lf_schedule_trigger`. The decisive lines are the `is_physical` branch, the
  `min_spacing` switch, the `#ifndef NDEBUG` clamp, and the final `lf_tag_compare(intended_tag,
  env->current_tag) == 0` increment. Check `lf_spacing_policy_t` for added or removed enumerators and
  compare with the current handbook "Actions" page.
- **Reactor model.** `grep -rn "theorem not_finitely_variable\|theorem weakly_finitely_variable\|theorem
  deterministic" ReactorModel/` and `grep -rn sorry --include=*.lean .`; a `lake build` replays the proofs.
  `grep -rni physical --include=*.lean .` returning matches would mean the model's scope has grown.
- **Causality.** In Zélus, check that `compiler/analysis/causality.ml` still types the arguments of
  `Eunarypre`, the second argument of `Efby`, and `Eup` against `Causal.new_var ()`, and that
  declarations still call `generalise` and `Global.set_causality`. In Vélus, check the `Eapp` clause of the
  dependency collector in `LCausality.v`; if it becomes per-output, node instances are no longer atomic
  and Findings 6 and 7 change.
- **RTIC.** Diff the two `lock` functions and `Ownership` in `analyze.rs`. If `main.rs` starts emitting a
  wait instruction for the idle case, Finding 8's last paragraph and invariant 5 of Finding 12 need a
  check of the new sequence against Probe C's pending-flag model.
- **SRP and wake-up models.** Re-run Probes B and C; expected final lines are `SRP_INVARIANTS_HOLD` and
  `EXPECTED_OUTCOME`. To test a different protocol shape, edit the `step` function of the relevant model;
  a reported trace is a concrete interleaving to check against the real code.
- **Mechanised coverage.** For Bedrock2, `grep -rni interrupt --include=*.v .` and re-read `goodHlTrace`;
  a non-polling alternative in that regular expression would be the first sign of interrupt support. For
  Pancake, check whether `panLangScript.sml` gains constructs other than `ExtCall`, `ShMemLoad` and
  `ShMemStore` for device interaction and whether the compiler's top-level theorem mentions entry
  points other than `main`. For Prosa, re-read the overview of results for rows naming a locking
  protocol or resource ceilings.
- **No cheap revalidation exists** for the hardware-dependent parts of Finding 10 (wait instructions and
  pending latches); they require reading the relevant architecture manual for the target core.
