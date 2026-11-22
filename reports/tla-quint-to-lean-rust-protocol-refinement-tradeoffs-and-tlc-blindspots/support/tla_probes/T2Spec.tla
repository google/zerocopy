------------------------------ MODULE T2Spec ------------------------------
(*
 * T2 (Crash-fsync 2PC / Lease-Raft Slice): Minimal 2PC / Single-Decree Lease-Raft Slice with
 * Asynchronous Adversarial Network, Crash-Restart Volatile RAM Wipe,
 * and Explicit `fsync` Durability Barrier.
 *
 * Mirrors the Lean crash-fsync 2PC / single-decree Lease-Raft benchmark 1-to-1.
 * Supports negative-control invariant hunting via `CONSTANT GuardFsync`:
 *   - `T2Spec.cfg` sets `GuardFsync = TRUE` (Agreement & DurabilityInv HOLD)
 *   - `MC_hunt_fsync.cfg` sets `GuardFsync = FALSE` (M1 bug CAUGHT by TLC!)
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT GuardFsync

Nodes == {0, 1, 2}
Terms == {1, 2}
Values == {1, 2}
QuorumSize == 2
NoneVal == 0
NoneEntry == [term |-> 0, val |-> 0]

LeaderOf(t) == IF t = 1 THEN 0 ELSE IF t = 2 THEN 2 ELSE 1

VARIABLES
    volTerm,        \* [Nodes -> 0..2]
    volRole,        \* [Nodes -> {"follower", "candidate", "leader"}]
    volLog,         \* [Nodes -> SUBSET [term: Terms, val: Values]]
    volDirty,       \* [Nodes -> BOOLEAN]
    volPendingVal,  \* [Nodes -> 0..2] (0 = none)
    volCommitted,   \* [Nodes -> 0..2] (0 = none)
    crashed,        \* [Nodes -> BOOLEAN]
    diskTerm,       \* [Nodes -> 0..2]
    diskLog,        \* [Nodes -> SUBSET [term: Terms, val: Values]]
    net             \* Monotonic set of sent messages (adversarial drop/dup/reorder)

vars == <<volTerm, volRole, volLog, volDirty, volPendingVal, volCommitted,
          crashed, diskTerm, diskLog, net>>

MaxTermEntry(entries) ==
    IF entries = {} THEN NoneEntry
    ELSE CHOOSE e \in entries : \A e2 \in entries : e.term >= e2.term

VotersFor(t) ==
    { n \in Nodes : \E m \in net : m.type = "VoteGrant" /\ m.term = t /\ m.voter = n }

ReportedEntries(t) ==
    { m.lastEntry : m \in { msg \in net : msg.type = "VoteGrant" /\ msg.term = t /\ msg.lastEntry /= NoneEntry } }

PrepareAckers(t, v) ==
    { n \in Nodes : [type |-> "PrepareAck", term |-> t, val |-> v, voter |-> n] \in net }

Init ==
    /\ volTerm = [n \in Nodes |-> 0]
    /\ volRole = [n \in Nodes |-> "follower"]
    /\ volLog = [n \in Nodes |-> {}]
    /\ volDirty = [n \in Nodes |-> FALSE]
    /\ volPendingVal = [n \in Nodes |-> NoneVal]
    /\ volCommitted = [n \in Nodes |-> NoneVal]
    /\ crashed = [n \in Nodes |-> FALSE]
    /\ diskTerm = [n \in Nodes |-> 0]
    /\ diskLog = [n \in Nodes |-> {}]
    /\ net = {}

StartElection(n, t) ==
    /\ n \in Nodes /\ t \in Terms
    /\ n = LeaderOf(t)
    /\ ~crashed[n]
    /\ volTerm[n] < t
    /\ volTerm' = [volTerm EXCEPT ![n] = t]
    /\ volRole' = [volRole EXCEPT ![n] = "candidate"]
    /\ volDirty' = [volDirty EXCEPT ![n] = TRUE]
    /\ volPendingVal' = [volPendingVal EXCEPT ![n] = NoneVal]
    /\ net' = net \cup {[type |-> "ReqVote", term |-> t, cand |-> n]}
    /\ UNCHANGED <<volLog, volCommitted, crashed, diskTerm, diskLog>>

RecvReqVote(n, t, cand) ==
    /\ n \in Nodes /\ t \in Terms /\ cand \in Nodes
    /\ [type |-> "ReqVote", term |-> t, cand |-> cand] \in net
    /\ ~crashed[n]
    /\ volTerm[n] < t
    /\ volTerm' = [volTerm EXCEPT ![n] = t]
    /\ volRole' = [volRole EXCEPT ![n] = "follower"]
    /\ volDirty' = [volDirty EXCEPT ![n] = TRUE]
    /\ volPendingVal' = [volPendingVal EXCEPT ![n] = NoneVal]
    /\ UNCHANGED <<volLog, volCommitted, crashed, diskTerm, diskLog, net>>

Fsync(n) ==
    /\ n \in Nodes
    /\ ~crashed[n]
    /\ volDirty[n]
    /\ volDirty' = [volDirty EXCEPT ![n] = FALSE]
    /\ diskTerm' = [diskTerm EXCEPT ![n] = volTerm[n]]
    /\ diskLog' = [diskLog EXCEPT ![n] = volLog[n]]
    /\ UNCHANGED <<volTerm, volRole, volLog, volPendingVal, volCommitted, crashed, net>>

SendVoteGrant(n, t) ==
    /\ n \in Nodes /\ t \in Terms
    /\ ~crashed[n]
    /\ volTerm[n] = t
    /\ ~(\E e \in volLog[n] : e.term = t)
    /\ (GuardFsync => (~volDirty[n] /\ diskTerm[n] = t))
    /\ LET srcLog == IF GuardFsync THEN diskLog[n] ELSE volLog[n]
           best == MaxTermEntry(srcLog)
       IN
       /\ [type |-> "VoteGrant", term |-> t, voter |-> n, lastEntry |-> best] \notin net
       /\ net' = net \cup {[type |-> "VoteGrant", term |-> t, voter |-> n, lastEntry |-> best]}
    /\ UNCHANGED <<volTerm, volRole, volLog, volDirty, volPendingVal, volCommitted,
                   crashed, diskTerm, diskLog>>

Propose(n, t, v) ==
    /\ n \in Nodes /\ t \in Terms /\ v \in Values
    /\ n = LeaderOf(t)
    /\ ~crashed[n]
    /\ volTerm[n] = t
    /\ volRole[n] = "candidate"
    /\ ~volDirty[n]
    /\ Cardinality(VotersFor(t)) >= QuorumSize
    /\ LET reps == ReportedEntries(t)
       IN reps = {} \/ v = MaxTermEntry(reps).val
    /\ volRole' = [volRole EXCEPT ![n] = "leader"]
    /\ volLog' = [volLog EXCEPT ![n] = volLog[n] \cup {[term |-> t, val |-> v]}]
    /\ volPendingVal' = [volPendingVal EXCEPT ![n] = v]
    /\ volDirty' = [volDirty EXCEPT ![n] = TRUE]
    /\ net' = net \cup {[type |-> "Prepare", term |-> t, val |-> v, leader |-> n]}
    /\ UNCHANGED <<volTerm, volCommitted, crashed, diskTerm, diskLog>>

RecvPrepare(n, t, v) ==
    /\ n \in Nodes /\ t \in Terms /\ v \in Values
    /\ \E ldr \in Nodes : [type |-> "Prepare", term |-> t, val |-> v, leader |-> ldr] \in net
    /\ ~crashed[n]
    /\ volTerm[n] <= t
    /\ [term |-> t, val |-> v] \notin volLog[n]
    /\ volTerm' = [volTerm EXCEPT ![n] = t]
    /\ volLog' = [volLog EXCEPT ![n] = volLog[n] \cup {[term |-> t, val |-> v]}]
    /\ volDirty' = [volDirty EXCEPT ![n] = TRUE]
    /\ volRole' = [volRole EXCEPT ![n] = IF n = LeaderOf(t) THEN volRole[n] ELSE "follower"]
    /\ UNCHANGED <<volPendingVal, volCommitted, crashed, diskTerm, diskLog, net>>

SendPrepareAck(n, t, v) ==
    /\ n \in Nodes /\ t \in Terms /\ v \in Values
    /\ ~crashed[n]
    /\ volTerm[n] = t
    /\ [term |-> t, val |-> v] \in volLog[n]
    /\ (GuardFsync => (~volDirty[n] /\ diskTerm[n] = t /\ [term |-> t, val |-> v] \in diskLog[n]))
    /\ [type |-> "PrepareAck", term |-> t, val |-> v, voter |-> n] \notin net
    /\ net' = net \cup {[type |-> "PrepareAck", term |-> t, val |-> v, voter |-> n]}
    /\ UNCHANGED <<volTerm, volRole, volLog, volDirty, volPendingVal, volCommitted,
                   crashed, diskTerm, diskLog>>

Commit(n, v) ==
    /\ n \in Nodes /\ v \in Values
    /\ ~crashed[n]
    /\ volRole[n] = "leader"
    /\ volPendingVal[n] = v
    /\ volCommitted[n] = NoneVal
    /\ Cardinality(PrepareAckers(volTerm[n], v)) >= QuorumSize
    /\ volCommitted' = [volCommitted EXCEPT ![n] = v]
    /\ UNCHANGED <<volTerm, volRole, volLog, volDirty, volPendingVal,
                   crashed, diskTerm, diskLog, net>>

Crash(n) ==
    /\ n \in Nodes
    /\ ~crashed[n]
    /\ volTerm' = [volTerm EXCEPT ![n] = 0]
    /\ volRole' = [volRole EXCEPT ![n] = "follower"]
    /\ volLog' = [volLog EXCEPT ![n] = {}]
    /\ volDirty' = [volDirty EXCEPT ![n] = FALSE]
    /\ volPendingVal' = [volPendingVal EXCEPT ![n] = NoneVal]
    /\ crashed' = [crashed EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<volCommitted, diskTerm, diskLog, net>>

Restart(n) ==
    /\ n \in Nodes
    /\ crashed[n]
    /\ volTerm' = [volTerm EXCEPT ![n] = diskTerm[n]]
    /\ volRole' = [volRole EXCEPT ![n] = "follower"]
    /\ volLog' = [volLog EXCEPT ![n] = diskLog[n]]
    /\ volDirty' = [volDirty EXCEPT ![n] = FALSE]
    /\ volPendingVal' = [volPendingVal EXCEPT ![n] = NoneVal]
    /\ crashed' = [crashed EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<volCommitted, diskTerm, diskLog, net>>

Next ==
    \/ \E n \in Nodes, t \in Terms : StartElection(n, t)
    \/ \E n \in Nodes, t \in Terms, c \in Nodes : RecvReqVote(n, t, c)
    \/ \E n \in Nodes : Fsync(n)
    \/ \E n \in Nodes, t \in Terms : SendVoteGrant(n, t)
    \/ \E n \in Nodes, t \in Terms, v \in Values : Propose(n, t, v)
    \/ \E n \in Nodes, t \in Terms, v \in Values : RecvPrepare(n, t, v)
    \/ \E n \in Nodes, t \in Terms, v \in Values : SendPrepareAck(n, t, v)
    \/ \E n \in Nodes, v \in Values : Commit(n, v)
    \/ \E n \in Nodes : Crash(n)
    \/ \E n \in Nodes : Restart(n)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ volTerm \in [Nodes -> {0} \cup Terms]
    /\ diskTerm \in [Nodes -> {0} \cup Terms]
    /\ volDirty \in [Nodes -> BOOLEAN]
    /\ crashed \in [Nodes -> BOOLEAN]
    /\ volCommitted \in [Nodes -> {0} \cup Values]

Agreement ==
    \A i, j \in Nodes :
        (volCommitted[i] /= NoneVal /\ volCommitted[j] /= NoneVal)
            => volCommitted[i] = volCommitted[j]

DurabilityInv ==
    \A m \in net :
        m.type = "PrepareAck" =>
            (diskTerm[m.voter] >= m.term /\ [term |-> m.term, val |-> m.val] \in diskLog[m.voter])

=============================================================================
