// T2 (Crash-fsync 2PC / Lease-Raft Slice): Minimal 2PC / Single-Decree Lease-Raft Slice in Quint
// Mirrors T2Spec.tla (crash-fsync 2PC / single-decree Lease-Raft slice).
module T2Spec {
  type NodeId = int
  type Term = int
  type Val = int
  type LogEntry = { term: Term, val: Val }
  type Role = str

  type NetMsg =
    | ReqVote({ term: Term, cand: NodeId })
    | VoteGrant({ term: Term, voter: NodeId, lastEntry: LogEntry })
    | Prepare({ term: Term, val: Val, leader: NodeId })
    | PrepareAck({ term: Term, val: Val, voter: NodeId })

  pure val NODES: Set[NodeId] = Set(0, 1, 2)
  pure val TERMS: Set[Term] = Set(1, 2)
  pure val VALUES: Set[Val] = Set(1, 2)
  pure val QUORUM: int = 2
  pure val NONE_ENTRY: LogEntry = { term: 0, val: 0 }

  pure def leaderOf(t: Term): NodeId =
    if (t == 1) 0 else if (t == 2) 2 else 1

  pure def maxEntry(entries: Set[LogEntry]): LogEntry =
    entries.fold(NONE_ENTRY, (acc, e) => if (e.term >= acc.term) e else acc)

  var volTerm: NodeId -> Term
  var volRole: NodeId -> Role
  var volLog: NodeId -> Set[LogEntry]
  var volDirty: NodeId -> bool
  var volPendingVal: NodeId -> Val
  var volCommitted: NodeId -> Val
  var crashed: NodeId -> bool
  var diskTerm: NodeId -> Term
  var diskLog: NodeId -> Set[LogEntry]
  var net: Set[NetMsg]

  action init = all {
    volTerm' = NODES.mapBy(_ => 0),
    volRole' = NODES.mapBy(_ => "follower"),
    volLog' = NODES.mapBy(_ => Set()),
    volDirty' = NODES.mapBy(_ => false),
    volPendingVal' = NODES.mapBy(_ => 0),
    volCommitted' = NODES.mapBy(_ => 0),
    crashed' = NODES.mapBy(_ => false),
    diskTerm' = NODES.mapBy(_ => 0),
    diskLog' = NODES.mapBy(_ => Set()),
    net' = Set(),
  }

  action startElection(n: NodeId, t: Term): bool = all {
    n == leaderOf(t),
    not(crashed.get(n)),
    volTerm.get(n) < t,
    volTerm' = volTerm.set(n, t),
    volRole' = volRole.set(n, "candidate"),
    volDirty' = volDirty.set(n, true),
    volPendingVal' = volPendingVal.set(n, 0),
    net' = net.union(Set(ReqVote({ term: t, cand: n }))),
    volLog' = volLog,
    volCommitted' = volCommitted,
    crashed' = crashed,
    diskTerm' = diskTerm,
    diskLog' = diskLog,
  }

  action recvReqVote(n: NodeId, t: Term, cand: NodeId): bool = all {
    net.contains(ReqVote({ term: t, cand: cand })),
    not(crashed.get(n)),
    volTerm.get(n) < t,
    volTerm' = volTerm.set(n, t),
    volRole' = volRole.set(n, "follower"),
    volDirty' = volDirty.set(n, true),
    volPendingVal' = volPendingVal.set(n, 0),
    volLog' = volLog,
    volCommitted' = volCommitted,
    crashed' = crashed,
    diskTerm' = diskTerm,
    diskLog' = diskLog,
    net' = net,
  }

  action fsync(n: NodeId): bool = all {
    not(crashed.get(n)),
    volDirty.get(n),
    volDirty' = volDirty.set(n, false),
    diskTerm' = diskTerm.set(n, volTerm.get(n)),
    diskLog' = diskLog.set(n, volLog.get(n)),
    volTerm' = volTerm,
    volRole' = volRole,
    volLog' = volLog,
    volPendingVal' = volPendingVal,
    volCommitted' = volCommitted,
    crashed' = crashed,
    net' = net,
  }

  action sendVoteGrant(n: NodeId, t: Term): bool = all {
    not(crashed.get(n)),
    volTerm.get(n) == t,
    not(volDirty.get(n)),
    diskTerm.get(n) == t,
    net' = net.union(Set(VoteGrant({ term: t, voter: n, lastEntry: maxEntry(diskLog.get(n)) }))),
    volTerm' = volTerm,
    volRole' = volRole,
    volLog' = volLog,
    volDirty' = volDirty,
    volPendingVal' = volPendingVal,
    volCommitted' = volCommitted,
    crashed' = crashed,
    diskTerm' = diskTerm,
    diskLog' = diskLog,
  }

  action propose(n: NodeId, t: Term, v: Val): bool = {
    val voters = NODES.filter(m =>
      net.exists(msg => match msg {
        | VoteGrant(g) => g.term == t and g.voter == m
        | _ => false
      })
    )
    val reported = net.fold(Set(), (acc, msg) => match msg {
      | VoteGrant(g) =>
          if (g.term == t and g.lastEntry != NONE_ENTRY) acc.union(Set(g.lastEntry)) else acc
      | _ => acc
    })
    all {
      n == leaderOf(t),
      not(crashed.get(n)),
      volTerm.get(n) == t,
      volRole.get(n) == "candidate",
      not(volDirty.get(n)),
      voters.size() >= QUORUM,
      reported.size() == 0 or v == maxEntry(reported).val,
      volRole' = volRole.set(n, "leader"),
      volLog' = volLog.set(n, volLog.get(n).union(Set({ term: t, val: v }))),
      volPendingVal' = volPendingVal.set(n, v),
      volDirty' = volDirty.set(n, true),
      net' = net.union(Set(Prepare({ term: t, val: v, leader: n }))),
      volTerm' = volTerm,
      volCommitted' = volCommitted,
      crashed' = crashed,
      diskTerm' = diskTerm,
      diskLog' = diskLog,
    }
  }

  action recvPrepare(n: NodeId, t: Term, v: Val): bool = all {
    NODES.exists(ldr => net.contains(Prepare({ term: t, val: v, leader: ldr }))),
    not(crashed.get(n)),
    volTerm.get(n) <= t,
    not(volLog.get(n).contains({ term: t, val: v })),
    volTerm' = volTerm.set(n, t),
    volLog' = volLog.set(n, volLog.get(n).union(Set({ term: t, val: v }))),
    volDirty' = volDirty.set(n, true),
    volRole' = volRole.set(n, if (n == leaderOf(t)) volRole.get(n) else "follower"),
    volPendingVal' = volPendingVal,
    volCommitted' = volCommitted,
    crashed' = crashed,
    diskTerm' = diskTerm,
    diskLog' = diskLog,
    net' = net,
  }

  action sendPrepareAck(n: NodeId, t: Term, v: Val): bool = all {
    not(crashed.get(n)),
    volTerm.get(n) == t,
    volLog.get(n).contains({ term: t, val: v }),
    not(volDirty.get(n)),
    diskTerm.get(n) == t,
    diskLog.get(n).contains({ term: t, val: v }),
    net' = net.union(Set(PrepareAck({ term: t, val: v, voter: n }))),
    volTerm' = volTerm,
    volRole' = volRole,
    volLog' = volLog,
    volDirty' = volDirty,
    volPendingVal' = volPendingVal,
    volCommitted' = volCommitted,
    crashed' = crashed,
    diskTerm' = diskTerm,
    diskLog' = diskLog,
  }

  action commit(n: NodeId, v: Val): bool = {
    val ackers = NODES.filter(m =>
      net.contains(PrepareAck({ term: volTerm.get(n), val: v, voter: m }))
    )
    all {
      not(crashed.get(n)),
      volRole.get(n) == "leader",
      volPendingVal.get(n) == v,
      ackers.size() >= QUORUM,
      volCommitted' = volCommitted.set(n, v),
      volTerm' = volTerm,
      volRole' = volRole,
      volLog' = volLog,
      volDirty' = volDirty,
      volPendingVal' = volPendingVal,
      crashed' = crashed,
      diskTerm' = diskTerm,
      diskLog' = diskLog,
      net' = net,
    }
  }

  action crash(n: NodeId): bool = all {
    not(crashed.get(n)),
    volTerm' = volTerm.set(n, 0),
    volRole' = volRole.set(n, "follower"),
    volLog' = volLog.set(n, Set()),
    volDirty' = volDirty.set(n, false),
    volPendingVal' = volPendingVal.set(n, 0),
    crashed' = crashed.set(n, true),
    volCommitted' = volCommitted,
    diskTerm' = diskTerm,
    diskLog' = diskLog,
    net' = net,
  }

  action restart(n: NodeId): bool = all {
    crashed.get(n),
    volTerm' = volTerm.set(n, diskTerm.get(n)),
    volRole' = volRole.set(n, "follower"),
    volLog' = volLog.set(n, diskLog.get(n)),
    volDirty' = volDirty.set(n, false),
    volPendingVal' = volPendingVal.set(n, 0),
    crashed' = crashed.set(n, false),
    volCommitted' = volCommitted,
    diskTerm' = diskTerm,
    diskLog' = diskLog,
    net' = net,
  }

  action step = {
    nondet n = oneOf(NODES)
    nondet t = oneOf(TERMS)
    nondet v = oneOf(VALUES)
    nondet c = oneOf(NODES)
    any {
      startElection(n, t),
      recvReqVote(n, t, c),
      fsync(n),
      sendVoteGrant(n, t),
      propose(n, t, v),
      recvPrepare(n, t, v),
      sendPrepareAck(n, t, v),
      commit(n, v),
      crash(n),
      restart(n),
    }
  }

  val agreementInv: bool =
    NODES.forall(i => NODES.forall(j =>
      (volCommitted.get(i) != 0 and volCommitted.get(j) != 0)
        implies (volCommitted.get(i) == volCommitted.get(j))
    ))

  val durabilityInv: bool =
    net.forall(msg => match msg {
      | PrepareAck(a) =>
          diskTerm.get(a.voter) >= a.term and
          diskLog.get(a.voter).contains({ term: a.term, val: a.val })
      | _ => true
    })
}
