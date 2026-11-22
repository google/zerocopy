------------------------------ MODULE H1Spec ------------------------------
(*
 * STRICTLY SEALED BLIND HOLDOUT PROTOCOL H1:
 * Lease-Fenced Reconfigurable Primary-Backup Replication
 *
 * Mirrors `H1Bench.lean` 1-to-1.
 *   - `GuardEpochFence = TRUE`: Stale primary writes are fenced; `NoStaleClobber`
 *     and `CrashDurability` HOLD across all reachable states.
 *   - `GuardEpochFence = FALSE`: `H1_Bug` allows stale epoch-1 writes to clobber
 *     node 1 after failover to epoch 2!
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT GuardEpochFence

Nodes == {0, 1, 2}
Epochs == {1, 2}
Values == {1, 2}
NoneVal == 0

PrimaryOf(e) == IF e = 1 THEN 0 ELSE 1
BackupOf(e) == IF e = 1 THEN 1 ELSE 2

VARIABLES
    volEpoch,
    volVal,
    volDirty,
    crashed,
    diskEpoch,
    diskVal,
    clobbered,
    committed,
    net

vars == <<volEpoch, volVal, volDirty, crashed, diskEpoch, diskVal,
          clobbered, committed, net>>

Init ==
    /\ volEpoch = [n \in Nodes |-> IF n <= 1 THEN 1 ELSE 0]
    /\ volVal = [n \in Nodes |-> NoneVal]
    /\ volDirty = [n \in Nodes |-> FALSE]
    /\ crashed = [n \in Nodes |-> FALSE]
    /\ diskEpoch = [n \in Nodes |-> IF n <= 1 THEN 1 ELSE 0]
    /\ diskVal = [n \in Nodes |-> NoneVal]
    /\ clobbered = [n \in Nodes |-> FALSE]
    /\ committed = [e \in Epochs |-> NoneVal]
    /\ net = {}

PrimaryWrite(p, e, v) ==
    /\ p \in Nodes /\ e \in Epochs /\ v \in Values
    /\ p = PrimaryOf(e)
    /\ ~crashed[p]
    /\ volEpoch[p] = e
    /\ diskEpoch[p] = e
    /\ ~volDirty[p]
    /\ volVal' = [volVal EXCEPT ![p] = v]
    /\ volDirty' = [volDirty EXCEPT ![p] = TRUE]
    /\ net' = net \cup {[type |-> "Replicate", epoch |-> e, val |-> v, primary |-> p]}
    /\ UNCHANGED <<volEpoch, crashed, diskEpoch, diskVal, clobbered, committed>>

BackupRecv(b, e, v) ==
    /\ b \in Nodes /\ e \in Epochs /\ v \in Values
    /\ b = BackupOf(e)
    /\ [type |-> "Replicate", epoch |-> e, val |-> v, primary |-> PrimaryOf(e)] \in net
    /\ ~crashed[b]
    /\ (GuardEpochFence => (volEpoch[b] <= e /\ diskEpoch[b] <= e))
    /\ volEpoch' = [volEpoch EXCEPT ![b] = e]
    /\ volVal' = [volVal EXCEPT ![b] = v]
    /\ volDirty' = [volDirty EXCEPT ![b] = TRUE]
    /\ clobbered' = [clobbered EXCEPT ![b] = clobbered[b] \/ (e < diskEpoch[b])]
    /\ UNCHANGED <<crashed, diskEpoch, diskVal, committed, net>>

Fsync(n) ==
    /\ n \in Nodes
    /\ ~crashed[n]
    /\ volDirty[n]
    /\ volDirty' = [volDirty EXCEPT ![n] = FALSE]
    /\ diskEpoch' = [diskEpoch EXCEPT ![n] = volEpoch[n]]
    /\ diskVal' = [diskVal EXCEPT ![n] = volVal[n]]
    /\ UNCHANGED <<volEpoch, volVal, crashed, clobbered, committed, net>>

BackupSendAck(b, e, v) ==
    /\ b \in Nodes /\ e \in Epochs /\ v \in Values
    /\ b = BackupOf(e)
    /\ ~crashed[b]
    /\ volEpoch[b] = e
    /\ volVal[b] = v
    /\ ~volDirty[b]
    /\ diskEpoch[b] = e
    /\ diskVal[b] = v
    /\ net' = net \cup {[type |-> "ReplAck", epoch |-> e, val |-> v, backup |-> b]}
    /\ UNCHANGED <<volEpoch, volVal, volDirty, crashed, diskEpoch, diskVal,
                   clobbered, committed>>

PrimaryCommit(p, e, v) ==
    /\ p \in Nodes /\ e \in Epochs /\ v \in Values
    /\ p = PrimaryOf(e)
    /\ ~crashed[p]
    /\ volEpoch[p] = e
    /\ volVal[p] = v
    /\ ~volDirty[p]
    /\ diskEpoch[p] = e
    /\ diskVal[p] = v
    /\ [type |-> "ReplAck", epoch |-> e, val |-> v, backup |-> BackupOf(e)] \in net
    /\ committed' = [committed EXCEPT ![e] = v]
    /\ UNCHANGED <<volEpoch, volVal, volDirty, crashed, diskEpoch, diskVal,
                   clobbered, net>>

StartFailover(newP, newE) ==
    /\ newP \in Nodes /\ newE = 2
    /\ newP = PrimaryOf(newE)
    /\ ~crashed[newP]
    /\ volEpoch[newP] < newE
    /\ ~volDirty[newP]
    /\ volEpoch' = [volEpoch EXCEPT ![newP] = newE]
    /\ volDirty' = [volDirty EXCEPT ![newP] = TRUE]
    /\ net' = net \cup {[type |-> "Fence", newEpoch |-> newE, newPrimary |-> newP]}
    /\ UNCHANGED <<volVal, crashed, diskEpoch, diskVal, clobbered, committed>>

Crash(n) ==
    /\ n \in Nodes
    /\ ~crashed[n]
    /\ volEpoch' = [volEpoch EXCEPT ![n] = 0]
    /\ volVal' = [volVal EXCEPT ![n] = NoneVal]
    /\ volDirty' = [volDirty EXCEPT ![n] = FALSE]
    /\ crashed' = [crashed EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<diskEpoch, diskVal, clobbered, committed, net>>

Restart(n) ==
    /\ n \in Nodes
    /\ crashed[n]
    /\ volEpoch' = [volEpoch EXCEPT ![n] = diskEpoch[n]]
    /\ volVal' = [volVal EXCEPT ![n] = diskVal[n]]
    /\ volDirty' = [volDirty EXCEPT ![n] = FALSE]
    /\ crashed' = [crashed EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<diskEpoch, diskVal, clobbered, committed, net>>

Next ==
    \/ \E p \in Nodes, e \in Epochs, v \in Values : PrimaryWrite(p, e, v)
    \/ \E b \in Nodes, e \in Epochs, v \in Values : BackupRecv(b, e, v)
    \/ \E n \in Nodes : Fsync(n)
    \/ \E b \in Nodes, e \in Epochs, v \in Values : BackupSendAck(b, e, v)
    \/ \E p \in Nodes, e \in Epochs, v \in Values : PrimaryCommit(p, e, v)
    \/ \E p \in Nodes : StartFailover(p, 2)
    \/ \E n \in Nodes : Crash(n)
    \/ \E n \in Nodes : Restart(n)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ volEpoch \in [Nodes -> {0} \cup Epochs]
    /\ diskEpoch \in [Nodes -> {0} \cup Epochs]
    /\ volVal \in [Nodes -> {0} \cup Values]
    /\ diskVal \in [Nodes -> {0} \cup Values]
    /\ volDirty \in [Nodes -> BOOLEAN]
    /\ crashed \in [Nodes -> BOOLEAN]
    /\ clobbered \in [Nodes -> BOOLEAN]

NoStaleClobber ==
    \A n \in Nodes : ~clobbered[n]

CrashDurability ==
    \A m \in net :
        m.type = "ReplAck" => diskEpoch[m.backup] >= m.epoch

=============================================================================
