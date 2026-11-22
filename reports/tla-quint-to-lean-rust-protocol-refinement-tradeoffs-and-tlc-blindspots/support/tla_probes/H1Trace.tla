------------------------------ MODULE H1Trace ------------------------------
(*
 * NDJSON-style Trace Validation Specification for H1 (Lease-Fenced Reconfigurable Primary-Backup).
 *)

EXTENDS H1Spec, TraceData, Sequences, TLC

VARIABLE l

trace_vars == <<vars, l>>
TraceView == <<vars, l>>

logline == TraceLog[l]

IsEvent(name) ==
    /\ l <= Len(TraceLog)
    /\ logline.event = name

ValidatePostStateNode(n) ==
    /\ ("vol_epoch" \in DOMAIN logline => volEpoch'[n] = logline.vol_epoch)
    /\ ("vol_val" \in DOMAIN logline => volVal'[n] = logline.vol_val)
    /\ ("vol_dirty" \in DOMAIN logline => volDirty'[n] = logline.vol_dirty)
    /\ ("disk_epoch" \in DOMAIN logline => diskEpoch'[n] = logline.disk_epoch)
    /\ ("disk_val" \in DOMAIN logline => diskVal'[n] = logline.disk_val)
    /\ ("crashed" \in DOMAIN logline => crashed'[n] = logline.crashed)

TracePrimaryWrite ==
    /\ IsEvent("PrimaryWrite")
    /\ LET p == logline.node
           e == logline.epoch
           v == logline.val
       IN
       /\ PrimaryWrite(p, e, v)
       /\ ValidatePostStateNode(p)
       /\ l' = l + 1

TraceBackupRecv ==
    /\ IsEvent("BackupRecv")
    /\ LET b == logline.node
           e == logline.epoch
           v == logline.val
       IN
       /\ BackupRecv(b, e, v)
       /\ ValidatePostStateNode(b)
       /\ l' = l + 1

TraceFsync ==
    /\ IsEvent("Fsync")
    /\ LET n == logline.node IN
       /\ Fsync(n)
       /\ ValidatePostStateNode(n)
       /\ l' = l + 1

TraceBackupSendAck ==
    /\ IsEvent("BackupSendAck")
    /\ LET b == logline.node
           e == logline.epoch
           v == logline.val
       IN
       /\ BackupSendAck(b, e, v)
       /\ ValidatePostStateNode(b)
       /\ l' = l + 1

TracePrimaryCommit ==
    /\ IsEvent("PrimaryCommit")
    /\ LET p == logline.node
           e == logline.epoch
           v == logline.val
       IN
       /\ PrimaryCommit(p, e, v)
       /\ ValidatePostStateNode(p)
       /\ ("committed" \in DOMAIN logline => committed'[e] = logline.committed)
       /\ l' = l + 1

TraceStartFailover ==
    /\ IsEvent("StartFailover")
    /\ LET p == logline.node
           e == logline.epoch
       IN
       /\ StartFailover(p, e)
       /\ ValidatePostStateNode(p)
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
    \/ TracePrimaryWrite
    \/ TraceBackupRecv
    \/ TraceFsync
    \/ TraceBackupSendAck
    \/ TracePrimaryCommit
    \/ TraceStartFailover
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
