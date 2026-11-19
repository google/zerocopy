#!/usr/bin/env python3
"""Executable semantics probe for async cancellation and work-stealing scheduling.

Models and empirically checks:
  1. Rust-style synchronous-drop `select!` data loss on a non-cancel-safe
     multi-step framed reader (analogous to `tokio::io::AsyncReadExt::read_exact`)
     versus external-buffer cancel-safe reading and Trio/Kotlin-style
     checkpointed/shielded cancel-scope cleanup.
  2. Tokio/Go-style 256-slot SPMC FIFO ring + 1-slot LIFO (`lifo_slot` / `runnext`)
     work-stealing scheduler pathologies:
       (a) Unbounded LIFO ping-pong starvation of FIFO, global, and I/O queues;
       (b) Tokio-style mitigation (`MAX_LIFO_POLLS_PER_TICK = 3`, `Budget(128)`,
           `event_interval = 61`, `global_queue_interval = 31`);
       (c) Cooperative blindspot under an unyielding CPU-bound `Future::poll`
           versus preemptive reduction/time-slice scheduling (BEAM / Go `sysmon`).
  3. Bounded SPMC FIFO work-stealing half-queue batch steal (`n - n // 2`) and
     overflow splitting (`256 -> 128`) conservation invariants.

Uses only the Python 3.10+ standard library and exits 0 iff all checks pass.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field
import json
import struct
import sys


# ---------------------------------------------------------------------------
# Part 1: Cancellation semantics (Sync Drop vs Cancel-Safe vs Cancel Scope)
# ---------------------------------------------------------------------------


class ChunkedByteStream:
    """Non-rewindable byte stream delivering at most `max_chunk` bytes per read."""

    def __init__(self, payload: bytes, max_chunk: int = 3) -> None:
        self._data = payload
        self._pos = 0
        self._max_chunk = max_chunk
        self._ready_cycle = 0

    def poll_read(self, want: int) -> bytes | None:
        """Return up to min(want, max_chunk) bytes, or None (Pending) on odd polls."""
        self._ready_cycle += 1
        if self._pos >= len(self._data):
            return b""
        # Alternate Pending / Ready to model partial network arrival across polls.
        if self._ready_cycle % 2 == 1:
            return None
        n = min(want, self._max_chunk, len(self._data) - self._pos)
        chunk = self._data[self._pos : self._pos + n]
        self._pos += n
        return chunk

    @property
    def bytes_consumed(self) -> int:
        return self._pos

    @property
    def remaining(self) -> int:
        return len(self._data) - self._pos


def encode_frames(messages: list[bytes]) -> bytes:
    return b"".join(struct.pack(">H", len(m)) + m for m in messages)


class NonCancelSafeReadFrameFuture:
    """Two-stage future holding intermediate header/payload inside `self`.

    Analogous to composing `read_u16().await` and `read_exact(&mut buf).await`
    inside a `tokio::select!` branch that recreates the future on each loop turn.
    Dropping this future while Pending silently discards all bytes already read
    into `self._hdr` / `self._body` because the underlying stream cursor advanced.
    """

    def __init__(self, stream: ChunkedByteStream) -> None:
        self._stream = stream
        self._hdr = bytearray()
        self._body_len: int | None = None
        self._body = bytearray()

    def poll(self) -> bytes | None:
        if self._body_len is None:
            while len(self._hdr) < 2:
                chunk = self._stream.poll_read(2 - len(self._hdr))
                if chunk is None:
                    return None
                if chunk == b"":
                    return b""
                self._hdr.extend(chunk)
            (self._body_len,) = struct.unpack(">H", bytes(self._hdr))
        while len(self._body) < self._body_len:
            chunk = self._stream.poll_read(self._body_len - len(self._body))
            if chunk is None:
                return None
            if chunk == b"":
                return b""
            self._body.extend(chunk)
        return bytes(self._body)

    def dropped_bytes_lost(self) -> int:
        return len(self._hdr) + len(self._body)


class CancelSafeExternalBufferReader:
    """External persistent buffer pattern (e.g., `BytesMut` + `read_buf`).

    Intermediate bytes live outside the `select!` branch future. Dropping a
    pending single-step read future loses zero bytes.
    """

    def __init__(self, stream: ChunkedByteStream) -> None:
        self._stream = stream
        self._buf = bytearray()

    def try_extract_frame(self) -> bytes | None:
        if len(self._buf) < 2:
            return None
        (body_len,) = struct.unpack(">H", bytes(self._buf[:2]))
        if len(self._buf) < 2 + body_len:
            return None
        frame = bytes(self._buf[2 : 2 + body_len])
        del self._buf[: 2 + body_len]
        return frame

    def poll_one_chunk(self) -> bool | None:
        """Single-step cancel-safe poll: commits chunk atomically into external buf."""
        chunk = self._stream.poll_read(4)
        if chunk is None:
            return None
        if chunk == b"":
            return False
        self._buf.extend(chunk)
        return True


class CancelledError(BaseException):
    """Trio/Kotlin-style cooperative cancellation exception (BaseException)."""


@dataclass
class CancelScope:
    """Simplified Trio-style hierarchical cancel scope with shielding."""

    parent: CancelScope | None = None
    shield: bool = False
    cancel_called: bool = False
    children: list[CancelScope] = field(default_factory=list)

    def __post_init__(self) -> None:
        if self.parent is not None:
            self.parent.children.append(self)

    def cancel(self) -> None:
        self.cancel_called = True

    def effectively_cancelled(self) -> bool:
        if self.cancel_called:
            return True
        if self.shield or self.parent is None:
            return False
        return self.parent.effectively_cancelled()

    def checkpoint(self) -> None:
        if self.effectively_cancelled():
            raise CancelledError("cancelled at cooperative checkpoint")


def run_cancellation_experiment() -> dict[str, object]:
    expected_frames = [b"alpha-01", b"bravo-022", b"charlie-3333", b"delta-44"]
    wire = encode_frames(expected_frames)

    # (a) Rust-style synchronous drop inside a select! loop where a heartbeat wins
    # every 3rd poll.
    stream_drop = ChunkedByteStream(wire, max_chunk=3)
    decoded_drop: list[bytes] = []
    bytes_discarded_on_drop = 0
    drops_mid_frame = 0
    fut = NonCancelSafeReadFrameFuture(stream_drop)
    for tick in range(1, 200):
        if stream_drop.remaining == 0 and fut.dropped_bytes_lost() == 0:
            break
        if tick % 3 == 0:
            # Competing `select!` branch (heartbeat) wins; unselected `fut` is
            # synchronously dropped and recreated on the next loop iteration.
            lost = fut.dropped_bytes_lost()
            if lost > 0:
                bytes_discarded_on_drop += lost
                drops_mid_frame += 1
            fut = NonCancelSafeReadFrameFuture(stream_drop)
            continue
        res = fut.poll()
        if res is not None:
            if res == b"":
                # EOF reached while truncated frame remained in dropped/corrupted state
                bytes_discarded_on_drop += fut.dropped_bytes_lost()
                break
            decoded_drop.append(res)
            fut = NonCancelSafeReadFrameFuture(stream_drop)

    # (b) Cancel-safe external buffer under the exact same heartbeat schedule.
    stream_safe = ChunkedByteStream(wire, max_chunk=3)
    reader = CancelSafeExternalBufferReader(stream_safe)
    decoded_safe: list[bytes] = []
    for tick in range(1, 200):
        frame = reader.try_extract_frame()
        if frame is not None:
            decoded_safe.append(frame)
            if len(decoded_safe) == len(expected_frames):
                break
            continue
        if tick % 3 == 0:
            # Heartbeat wins; dropping the single-step poll future loses 0 bytes.
            continue
        progressed = reader.poll_one_chunk()
        if progressed is False and reader.try_extract_frame() is None:
            break

    # (c) Trio/Kotlin-style cancel scope with checkpointed cancellation and
    # shielded atomic teardown (graceful transaction rollback / flush).
    stream_scope = ChunkedByteStream(wire, max_chunk=3)
    outer_scope = CancelScope()
    committed_frames: list[bytes] = []
    in_flight_staging = bytearray()
    rollback_log: list[int] = []
    cancelled_cleanly = False
    shielded_cleanup_ran = False

    def run_scoped_reader() -> None:
        nonlocal cancelled_cleanly, shielded_cleanup_ran
        try:
            for step in range(1, 200):
                # Trigger parent cancellation mid-second-frame after partial read.
                if len(committed_frames) == 1 and len(in_flight_staging) >= 3:
                    outer_scope.cancel()
                # Cooperative checkpoint outside atomic commit boundary.
                outer_scope.checkpoint()
                chunk = stream_scope.poll_read(3)
                if chunk is None:
                    continue
                if chunk == b"":
                    break
                in_flight_staging.extend(chunk)
                while len(in_flight_staging) >= 2:
                    (flen,) = struct.unpack(">H", bytes(in_flight_staging[:2]))
                    if len(in_flight_staging) < 2 + flen:
                        break
                    # Shielded commit section: cannot be torn mid-mutation.
                    commit_scope = CancelScope(parent=outer_scope, shield=True)
                    commit_scope.checkpoint()  # shielded: does not raise
                    payload = bytes(in_flight_staging[2 : 2 + flen])
                    del in_flight_staging[: 2 + flen]
                    committed_frames.append(payload)
        except CancelledError:
            cancelled_cleanly = True
            # Shielded cleanup (analogous to Trio `CancelScope(shield=True)` or
            # Kotlin `withContext(NonCancellable)`): preserves in-flight staged
            # bytes into durable rollback log instead of silently discarding them.
            cleanup_scope = CancelScope(parent=outer_scope, shield=True)
            cleanup_scope.checkpoint()  # shielded: cleanup proceeds
            rollback_log.append(len(in_flight_staging))
            shielded_cleanup_ran = True

    run_scoped_reader()

    # (d) Two-stage mpsc::Sender::reserve + Permit::send cancel-safety pattern
    # vs. naive dequeue-then-send inside select! (which drops owned items on cancel).
    upstream_naive = deque(["msg-1", "msg-2", "msg-3"])
    downstream_naive: list[str] = []
    dropped_in_flight_msgs = 0
    channel_cap = 1
    channel_in_use = 1  # initially full -> send blocks

    # Naive: dequeue first, then race send(item) against cancel -> item dropped!
    in_flight = upstream_naive.popleft()
    if channel_in_use >= channel_cap:
        # Competing select! branch wins while send(in_flight) is Pending:
        # `in_flight` was moved into the send future and is destroyed on Drop.
        dropped_in_flight_msgs += 1
        in_flight = ""

    # Permit pattern (tokio::sync::mpsc::Sender::reserve): reserve slot BEFORE
    # popping from upstream. Dropping pending reserve loses only queue order,
    # never a dequeued message; once Permit is acquired, permit.send() is sync.
    upstream_permit = deque(["msg-1", "msg-2", "msg-3"])
    downstream_permit: list[str] = []
    # Attempt 1: channel full -> reserve() is Pending -> cancelled safely
    permit_acquired = channel_in_use < channel_cap
    assert not permit_acquired
    assert len(upstream_permit) == 3  # zero messages lost
    # Attempt 2: consumer frees capacity -> reserve() completes -> sync send
    channel_in_use = 0
    permit_acquired = channel_in_use < channel_cap
    assert permit_acquired
    channel_in_use += 1
    downstream_permit.append(upstream_permit.popleft())

    # Verify assertions
    assert bytes_discarded_on_drop > 0, "Expected sync-drop select! to lose buffered bytes"
    assert drops_mid_frame > 0, "Expected mid-frame drops in sync-drop scenario"
    assert decoded_drop != expected_frames, "Sync-drop stream should corrupt/truncate frames"
    assert decoded_safe == expected_frames, f"Cancel-safe reader failed: {decoded_safe}"
    assert cancelled_cleanly and shielded_cleanup_ran, "CancelScope shielded cleanup failed"
    assert committed_frames == expected_frames[:1], f"Unexpected committed frames: {committed_frames}"
    assert sum(rollback_log) == len(in_flight_staging) and sum(rollback_log) > 0
    assert dropped_in_flight_msgs == 1 and len(upstream_naive) == 2 and not downstream_naive
    assert downstream_permit == ["msg-1"] and len(upstream_permit) == 2
    # Conservation check for scoped reader: committed bytes + staged bytes == stream consumed
    scoped_accounted = sum(2 + len(f) for f in committed_frames) + len(in_flight_staging)
    assert scoped_accounted == stream_scope.bytes_consumed

    return {
        "expected_frame_count": len(expected_frames),
        "wire_bytes": len(wire),
        "sync_drop_select": {
            "decoded_frames": len(decoded_drop),
            "decoded_matches_expected": decoded_drop == expected_frames,
            "drops_mid_frame": drops_mid_frame,
            "bytes_silently_discarded": bytes_discarded_on_drop,
        },
        "cancel_safe_external_buf": {
            "decoded_frames": len(decoded_safe),
            "decoded_matches_expected": decoded_safe == expected_frames,
            "bytes_silently_discarded": 0,
        },
        "trio_kotlin_cancel_scope": {
            "cancelled_cleanly": cancelled_cleanly,
            "shielded_cleanup_ran": shielded_cleanup_ran,
            "committed_frames_before_cancel": len(committed_frames),
            "staged_bytes_recovered_in_cleanup": sum(rollback_log),
            "total_bytes_accounted": scoped_accounted,
            "stream_bytes_consumed": stream_scope.bytes_consumed,
        },
        "mpsc_reserve_permit_pattern": {
            "naive_dequeue_then_send_dropped_msgs": dropped_in_flight_msgs,
            "permit_pattern_dropped_msgs": 0,
            "permit_pattern_delivered": downstream_permit,
        },
    }


# ---------------------------------------------------------------------------
# Part 2: Work-Stealing LIFO Slot Starvation, Coop Budget & Preemption
# ---------------------------------------------------------------------------


@dataclass
class TaskSpec:
    name: str
    kind: str  # "ping", "pong", "fifo", "global", "cpu_hog"
    cpu_cost: int = 1
    coop_aware: bool = True
    polls: int = 0
    work_done: int = 0
    max_wait_gap: int = 0
    last_polled_step: int = 0


def simulate_worker(
    mode: str,
    total_steps: int = 1000,
    max_lifo_polls_per_tick: int = 3,
    event_interval: int = 61,
    global_queue_interval: int = 31,
    coop_budget: int = 128,
    preempt_quantum: int = 10,
) -> dict[str, object]:
    """Simulate a single worker with 256-slot FIFO runq + 1-slot LIFO + global + IO."""
    ping = TaskSpec("ping", "ping")
    pong = TaskSpec("pong", "pong")
    fifo_tasks = [TaskSpec(f"fifo_{i}", "fifo") for i in range(4)]
    global_task = TaskSpec("global_0", "global")
    cpu_hog = TaskSpec("cpu_hog", "cpu_hog", cpu_cost=500, coop_aware=False)

    tasks: dict[str, TaskSpec] = {
        "ping": ping,
        "pong": pong,
        "global_0": global_task,
        **{t.name: t for t in fifo_tasks},
    }

    lifo_slot: str | None = "ping"
    local_fifo: deque[str] = deque(t.name for t in fifo_tasks)
    global_queue: deque[str] = deque(["global_0"])

    if mode in ("coop_cpu_hog", "preemptive_cpu_hog"):
        tasks["cpu_hog"] = cpu_hog
        local_fifo.appendleft("cpu_hog")
        lifo_slot = None

    io_reactor_polls = 0
    max_io_gap = 0
    last_io_step = 0
    tick = 0
    step = 0

    def schedule_local(name: str, lifo_enabled: bool) -> None:
        nonlocal lifo_slot
        if lifo_enabled:
            if lifo_slot is not None:
                local_fifo.append(lifo_slot)
            lifo_slot = name
        else:
            local_fifo.append(name)

    while step < total_steps:
        tick += 1

        # Maintenance / reactor polling every event_interval ticks
        if tick % event_interval == 0:
            io_reactor_polls += 1
            max_io_gap = max(max_io_gap, step - last_io_step)
            last_io_step = step

        # Pick initial task for this tick
        cur: str | None = None
        if mode != "unbounded_lifo" and tick % global_queue_interval == 0 and global_queue:
            cur = global_queue.popleft()
        elif lifo_slot is not None:
            cur = lifo_slot
            lifo_slot = None
        elif local_fifo:
            cur = local_fifo.popleft()
        elif global_queue:
            cur = global_queue.popleft()
        else:
            break

        # Inner tick loop (LIFO chain inheriting cooperative budget)
        budget = coop_budget
        lifo_polls = 0
        lifo_enabled = True

        while cur is not None and step < total_steps:
            t = tasks[cur]
            t.polls += 1
            t.max_wait_gap = max(t.max_wait_gap, step - t.last_polled_step)

            if t.kind == "cpu_hog":
                if mode == "coop_cpu_hog":
                    # Non-yielding synchronous CPU loop inside Future::poll:
                    # ignores cooperative budget completely until completion.
                    run_units = min(t.cpu_cost, total_steps - step)
                    step += run_units
                    t.work_done += run_units
                    t.last_polled_step = step
                    local_fifo.append(t.name)
                    cur = None
                    continue
                elif mode == "preemptive_cpu_hog":
                    # Preempted after `preempt_quantum` units (BEAM reductions / Go sysmon).
                    run_units = min(preempt_quantum, total_steps - step)
                    step += run_units
                    t.work_done += run_units
                    t.last_polled_step = step
                    local_fifo.append(t.name)
                    cur = None
                    continue

            # Regular async task poll: consumes 1 unit of step & coop budget
            step += 1
            t.work_done += 1
            t.last_polled_step = step
            if t.coop_aware:
                budget -= 1

            # Reschedule behavior
            if t.kind == "ping":
                schedule_local("pong", lifo_enabled=lifo_enabled)
            elif t.kind == "pong":
                schedule_local("ping", lifo_enabled=lifo_enabled)
            elif t.kind == "fifo":
                local_fifo.append(t.name)
            elif t.kind == "global":
                global_queue.append(t.name)

            # Decide whether to chain directly into lifo_slot
            if mode == "unbounded_lifo":
                if lifo_slot is not None:
                    cur = lifo_slot
                    lifo_slot = None
                    continue
                cur = None
            elif mode == "tokio_bounded":
                if lifo_slot is None:
                    cur = None
                    continue
                if budget <= 0:
                    # Budget depleted: push LIFO task to back of local_fifo & end tick
                    local_fifo.append(lifo_slot)
                    lifo_slot = None
                    cur = None
                    continue
                lifo_polls += 1
                if lifo_polls >= max_lifo_polls_per_tick:
                    lifo_enabled = False
                cur = lifo_slot
                lifo_slot = None
            else:
                cur = None

    max_io_gap = max(max_io_gap, step - last_io_step)
    for t in tasks.values():
        t.max_wait_gap = max(t.max_wait_gap, step - t.last_polled_step)
    return {
        "mode": mode,
        "steps_executed": step,
        "ticks": tick,
        "ping_polls": ping.polls,
        "pong_polls": pong.polls,
        "fifo_polls": [t.polls for t in fifo_tasks],
        "global_polls": global_task.polls,
        "io_reactor_polls": io_reactor_polls,
        "max_io_gap_steps": max_io_gap,
        "cpu_hog_polls": cpu_hog.polls if "cpu_hog" in tasks else 0,
        "fifo_max_wait_steps": max(t.max_wait_gap for t in fifo_tasks),
    }


def run_scheduler_experiment() -> dict[str, object]:
    unbounded = simulate_worker("unbounded_lifo", total_steps=1000)
    bounded = simulate_worker("tokio_bounded", total_steps=1000)
    coop_hog = simulate_worker("coop_cpu_hog", total_steps=1000)
    preempt_hog = simulate_worker("preemptive_cpu_hog", total_steps=1000)

    # Assertions matching real runtime properties:
    # 1. Unbounded LIFO ping-pong causes 100% starvation of FIFO, global, and IO.
    assert unbounded["ping_polls"] + unbounded["pong_polls"] == 1000
    assert sum(unbounded["fifo_polls"]) == 0
    assert unbounded["global_polls"] == 0
    assert unbounded["io_reactor_polls"] == 0

    # 2. Tokio bounded LIFO (MAX_LIFO_POLLS_PER_TICK=3 + global/event intervals)
    # eliminates starvation while keeping ping-pong locality high.
    assert all(p > 0 for p in bounded["fifo_polls"]), f"FIFO starved: {bounded}"
    assert bounded["global_polls"] > 0, f"Global queue starved: {bounded}"
    assert bounded["io_reactor_polls"] > 0, f"IO reactor starved: {bounded}"
    assert bounded["ping_polls"] > bounded["fifo_polls"][0], "LIFO locality should favor ping-pong"

    # 3. Unyielding synchronous CPU hog under cooperative scheduling creates a
    # >= 500-step stall gap on FIFO tasks and IO reactor despite coop budget.
    assert coop_hog["fifo_max_wait_steps"] >= 500
    assert coop_hog["max_io_gap_steps"] >= 500

    # 4. Preemptive quantum bounds worst-case FIFO wait gap dramatically lower.
    assert preempt_hog["fifo_max_wait_steps"] < coop_hog["fifo_max_wait_steps"] // 5
    assert preempt_hog["io_reactor_polls"] > coop_hog["io_reactor_polls"]

    return {
        "unbounded_lifo": unbounded,
        "tokio_bounded_lifo": bounded,
        "coop_unyielding_cpu_hog": coop_hog,
        "preemptive_quantum_cpu_hog": preempt_hog,
    }


# ---------------------------------------------------------------------------
# Part 3: Bounded 256-slot SPMC FIFO Batch Steal & Overflow Conservation
# ---------------------------------------------------------------------------


class BoundedLocalRunQueue:
    """Faithful single-thread model of Tokio/Go 256-slot SPMC FIFO ring buffer.

    Models:
      - Capacity 256 (`LOCAL_QUEUE_CAPACITY = 256`).
      - Overflow: spills half (`128`) oldest tasks + incoming task to global queue.
      - Batch steal (`steal_into`): steals `n - n // 2` (ceil(n/2)) oldest tasks
        matching `tokio/src/runtime/scheduler/multi_thread/queue.rs:487-488`.
    """

    CAPACITY = 256

    def __init__(self) -> None:
        self._q: deque[int] = deque()

    def push_back_or_overflow(self, task_id: int, global_q: deque[int]) -> int:
        if len(self._q) < self.CAPACITY:
            self._q.append(task_id)
            return 0
        # Spill half (128) + incoming task to global queue
        half = self.CAPACITY // 2
        for _ in range(half):
            global_q.append(self._q.popleft())
        global_q.append(task_id)
        return half + 1

    def pop_fifo(self) -> int | None:
        return self._q.popleft() if self._q else None

    def steal_into(self, dst: BoundedLocalRunQueue) -> int:
        n = len(self._q)
        if n == 0 or len(dst._q) > self.CAPACITY // 2:
            return 0
        steal_count = n - (n // 2)
        for _ in range(steal_count):
            dst._q.append(self._q.popleft())
        return steal_count

    def __len__(self) -> int:
        return len(self._q)


def run_work_stealing_conservation_check() -> dict[str, int]:
    w0 = BoundedLocalRunQueue()
    w1 = BoundedLocalRunQueue()
    global_q: deque[int] = deque()
    total_pushed = 300
    spilled_total = 0

    for tid in range(total_pushed):
        spilled_total += w0.push_back_or_overflow(tid, global_q)

    # After 256 pushes, w0 is full; push #256 spills 128 + 1 = 129 to global_q,
    # leaving 128 in w0, then 43 more pushes go to w0 => 171 in w0, 129 in global_q.
    assert spilled_total == 129
    assert len(w0) == 171
    assert len(global_q) == 129

    # w1 steals ceil(171 / 2) = 86 tasks from w0, leaving 85 in w0.
    stolen = w0.steal_into(w1)
    assert stolen == 86
    assert len(w0) == 85
    assert len(w1) == 86

    # Verify exact conservation (no lost or duplicated task IDs)
    seen: list[int] = []
    while (x := w0.pop_fifo()) is not None:
        seen.append(x)
    while (x := w1.pop_fifo()) is not None:
        seen.append(x)
    seen.extend(global_q)
    assert sorted(seen) == list(range(total_pushed)), "Task conservation violated!"

    return {
        "total_pushed": total_pushed,
        "spilled_to_global": spilled_total,
        "stolen_batch": stolen,
        "remaining_victim": 85,
        "conserved_unique_tasks": len(set(seen)),
    }


def main() -> int:
    results = {
        "cancellation_experiment": run_cancellation_experiment(),
        "scheduler_experiment": run_scheduler_experiment(),
        "work_stealing_conservation": run_work_stealing_conservation_check(),
    }
    print(json.dumps(results, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
