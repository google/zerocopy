------------------------------ MODULE T2Trace ------------------------------
(*
 * NDJSON / Quint ITF Trace Validation Specification for T2 (2PC / Lease-Raft Crash-fsync Slice).
 *
 * Replays flat NDJSON and Quint ITF JSON traces (loaded via `TraceData.tla`
 * adapter for TLC 2.15) against `T2Spec.tla` with `GuardFsync = TRUE`,
 * enforcing `IsEvent`, `ValidatePostStateNode`, cursor `l ∈ 1..Len(TraceLog)+1`,
 * `TraceView == <<vars, l>>`, and `TraceMatched == <>(l > Len(TraceLog))`.
 *)

EXTENDS T2Spec, TraceData, Sequences, TLC

VARIABLE l   \* Trace cursor: 1 .. Len(TraceLog) + 1

trace_vars == <<vars, l>>
TraceView == <<vars, l>>

logline == TraceLog[l]

IsEvent(name) ==
    /\ l <= Len(TraceLog)
    /\ logline.event = name

ValidatePostStateNode(n) ==
    /\ ("vol_term" \in DOMAIN logline => volTerm'[n] = logline.vol_term)
    /\ ("vol_role" \in DOMAIN logline => volRole'[n] = logline.vol_role)
    /\ ("vol_dirty" \in DOMAIN logline => volDirty'[n] = logline.vol_dirty)
    /\ ("disk_term" \in DOMAIN logline => diskTerm'[n] = logline.disk_term)
    /\ ("durable_log_len" \in DOMAIN logline => Cardinality(diskLog'[n]) = logline.durable_log_len)
    /\ ("committed" \in DOMAIN logline => volCommitted'[n] = logline.committed)
    /\ ("crashed" \in DOMAIN logline => crashed'[n] = logline.crashed)

TraceStartElection ==
    /\ IsEvent("StartElection")
    /\ LET n == logline.node
           t == logline.term
       IN
       /\ StartElection(n, t)
       /\ ValidatePostStateNode(n)
       /\ l' = l + 1

TraceRecvReqVote ==
    /\ IsEvent("RecvReqVote")
    /\ LET n == logline.node
           t == logline.term
           c == logline.cand
       IN
       /\ RecvReqVote(n, t, c)
       /\ ValidatePostStateNode(n)
       /\ l' = l + 1

TraceFsync ==
    /\ IsEvent("Fsync")
    /\ LET n == logline.node IN
       /\ Fsync(n)
       /\ ValidatePostStateNode(n)
       /\ l' = l + 1

TraceSendVoteGrant ==
    /\ IsEvent("SendVoteGrant")
    /\ LET n == logline.node
           t == logline.term
       IN
       /\ SendVoteGrant(n, t)
       /\ ValidatePostStateNode(n)
       /\ l' = l + 1

TracePropose ==
    /\ IsEvent("Propose")
    /\ LET n == logline.node
           t == logline.term
           v == logline.val
       IN
       /\ Propose(n, t, v)
       /\ ValidatePostStateNode(n)
       /\ l' = l + 1

TraceRecvPrepare ==
    /\ IsEvent("RecvPrepare")
    /\ LET n == logline.node
           t == logline.term
           v == logline.val
       IN
       /\ RecvPrepare(n, t, v)
       /\ ValidatePostStateNode(n)
       /\ l' = l + 1

TraceSendPrepareAck ==
    /\ IsEvent("SendPrepareAck")
    /\ LET n == logline.node
           t == logline.term
           v == logline.val
       IN
       /\ SendPrepareAck(n, t, v)
       /\ ValidatePostStateNode(n)
       /\ l' = l + 1

TraceCommit ==
    /\ IsEvent("Commit")
    /\ LET n == logline.node
           v == logline.val
       IN
       /\ Commit(n, v)
       /\ ValidatePostStateNode(n)
       /\ l' = l + 1

TraceCrash ==
    /\ IsEvent("Crash")
    /\ LET n == logline.node IN
       /\ Crash(n)
       /\ ValidatePostStateNode(n)
       /\ l' = l + 1

TraceRestart ==
    /\ IsEvent("Restart")
    /\ LET n == logline.node IN
       /\ Restart(n)
       /\ ValidatePostStateNode(n)
       /\ l' = l + 1

TraceAction ==
    \/ TraceStartElection
    \/ TraceRecvReqVote
    \/ TraceFsync
    \/ TraceSendVoteGrant
    \/ TracePropose
    \/ TraceRecvPrepare
    \/ TraceSendPrepareAck
    \/ TraceCommit
    \/ TraceCrash
    \/ TraceRestart

TraceInit ==
    /\ Init
    /\ l = 1

TraceNext ==
    IF l <= Len(TraceLog) THEN
        TraceAction
    ELSE
        UNCHANGED trace_vars

TraceSpec ==
    /\ TraceInit
    /\ [][TraceNext]_trace_vars
    /\ WF_trace_vars(TraceNext)

TraceMatched == <>(l > Len(TraceLog))

=============================================================================
