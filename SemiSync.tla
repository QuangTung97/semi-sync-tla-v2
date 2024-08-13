------ MODULE SemiSync ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS Replica, nil

VARIABLES
    next_req,
    db, db_leader, db_epoch, db_leader_epoch,
    db_replicas, db_replicated,
    zk_leader, zk_epoch, zk_leader_epoch, zk_replicas, zk_status,
    ctl_pc, ctl_epoch, ctl_leader, ctl_replicas, ctl_offset,
    client_log

zk_vars == <<zk_leader, zk_epoch, zk_leader_epoch, zk_replicas, zk_status>>
db_vars == <<db, db_leader, db_epoch, db_leader_epoch, db_replicas, db_replicated>>
ctl_vars == <<ctl_pc, ctl_epoch, ctl_leader, ctl_replicas, ctl_offset>>
global_vars == <<next_req, client_log>>

vars == <<global_vars, db_vars, zk_vars, ctl_vars>>

LogEntry == 41..50
EpochNumber == 11..30
NullLogEntry == LogEntry \union {nil}

max_req == 40 + 3


replicationFactor(n) == (n + 2) \div 2

quorumOfSet(S) ==
    {Q \in SUBSET S: Cardinality(Q) = replicationFactor(Cardinality(S))}

quorumOf(r) == quorumOfSet(db_replicas[r])


TypeOK ==
    /\ next_req \in LogEntry \union {40}

    /\ zk_leader \in Replica
    /\ zk_epoch \in EpochNumber
    /\ zk_leader_epoch \in EpochNumber
    /\ zk_replicas \subseteq Replica
    /\ zk_status \in {"Normal", "WaitReplicate", "FindNewLeader"}

    /\ zk_leader \in zk_replicas

    /\ db \in [Replica -> Seq(LogEntry)]
    /\ db_leader \in [Replica -> Replica]
    /\ db_epoch \in [Replica -> EpochNumber]
    /\ db_leader_epoch \in [Replica -> EpochNumber]
    /\ db_replicas \in [Replica -> SUBSET Replica]
    /\ db_replicated \in [Replica -> [Replica -> 0..10]]

    /\ ctl_pc \in {"Init", "CtlReadLeaderLog", "CtlReadReplicaLog", "Finished"}
    /\ ctl_epoch \in EpochNumber
    /\ ctl_leader \in Replica
    /\ ctl_replicas \subseteq Replica
    /\ ctl_offset \in [Replica -> 0..10]

    /\ client_log \in Seq(LogEntry)


Init ==
    /\ next_req = 40

    /\ zk_leader \in Replica
    /\ zk_epoch = 11
    /\ zk_leader_epoch = zk_epoch
    /\ zk_replicas = {zk_leader}
    /\ zk_status = "Normal"

    /\ db = [r \in Replica |-> <<>>]
    /\ db_leader = [r \in Replica |-> zk_leader]
    /\ db_epoch = [r \in Replica |-> zk_epoch]
    /\ db_leader_epoch = [r \in Replica |-> zk_epoch]
    /\ db_replicas = [r \in Replica |-> zk_replicas]
    /\ db_replicated = [r \in Replica |-> [r2 \in Replica |-> 0]]

    /\ ctl_pc = "Init"
    /\ ctl_epoch = zk_epoch
    /\ ctl_leader = zk_leader
    /\ ctl_replicas = zk_replicas
    /\ ctl_offset = [r \in Replica |-> 0]

    /\ client_log = <<>>


Terminated ==
    /\ UNCHANGED vars


AppendLog(r) ==
    /\ next_req < max_req
    /\ db_leader[r] = r
    /\ next_req' = next_req + 1
    /\ db' = [db EXCEPT ![r] = Append(@, next_req')]
    /\ db_replicated' = [db_replicated EXCEPT ![r][r] = Len(db'[r])]
    /\ UNCHANGED <<db_leader, db_epoch, db_leader_epoch, db_replicas>>
    /\ UNCHANGED client_log
    /\ UNCHANGED zk_vars
    /\ UNCHANGED ctl_vars


AppendClientLog(r) ==
    /\ db_leader[r] = r
    /\ LET n == Len(client_log) IN
        /\ n < Len(db[r])
        /\ \E Q \in quorumOf(r):
            \A r2 \in Q: db_replicated[r][r2] > n
        /\ client_log' = Append(client_log, db[r][n + 1])
    /\ UNCHANGED next_req
    /\ UNCHANGED db_vars
    /\ UNCHANGED zk_vars
    /\ UNCHANGED ctl_vars


ZkAddReplica(r) ==
    /\ ~(r \in zk_replicas)
    /\ zk_status = "Normal"
    /\ zk_replicas' = zk_replicas \union {r}
    /\ zk_epoch' = zk_epoch + 1
    /\ zk_status' = "WaitReplicate"
    /\ UNCHANGED <<zk_leader, zk_leader_epoch>>
    /\ UNCHANGED global_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED ctl_vars


ZkPrepareChangeLeader ==
    /\ Cardinality(zk_replicas) > 1
    /\ zk_status = "Normal"
    /\ zk_epoch' = zk_epoch + 1
    /\ zk_status' = "FindNewLeader"
    /\ UNCHANGED <<zk_leader, zk_replicas, zk_leader_epoch>>
    /\ UNCHANGED db_vars
    /\ UNCHANGED global_vars
    /\ UNCHANGED ctl_vars


DBUpdateZKInfo(r) ==
    /\ db_epoch[r] < zk_epoch
    /\ db_epoch' = [db_epoch EXCEPT ![r] = zk_epoch]
    /\ db_leader_epoch' = [db_leader_epoch EXCEPT ![r] = zk_leader_epoch]
    /\ db_leader' = [db_leader EXCEPT ![r] = zk_leader]
    /\ db_replicas' = [db_replicas EXCEPT ![r] = zk_replicas]
    /\ UNCHANGED db_replicated
    /\ UNCHANGED db
    /\ UNCHANGED zk_vars
    /\ UNCHANGED global_vars
    /\ UNCHANGED ctl_vars


DBReceveFromLeader(r) == LET leader == db_leader[r] IN
    /\ leader /= r
    /\ r \in db_replicas[r]
    /\ db_leader_epoch[r] = db_leader_epoch[leader]
    /\ Len(db[r]) < Len(db[leader])
    /\ LET n == Len(db[r]) IN
        /\ db' = [db EXCEPT ![r] = Append(@, db[leader][n + 1])]
    /\ UNCHANGED <<db_leader, db_epoch, db_leader_epoch, db_replicas, db_replicated>>
    /\ UNCHANGED zk_vars
    /\ UNCHANGED global_vars
    /\ UNCHANGED ctl_vars


DBUpdateReplicated(r, r1) ==
    /\ db_leader[r] = r
    /\ r1 /= r
    /\ db_leader_epoch[r] = db_leader_epoch[r1]
    /\ db_replicated[r][r1] < Len(db[r1])
    /\ db_replicated' = [db_replicated EXCEPT ![r][r1] = Len(db[r1])]
    /\ UNCHANGED <<db, db_epoch, db_leader, db_leader_epoch, db_replicas>>
    /\ UNCHANGED global_vars
    /\ UNCHANGED zk_vars
    /\ UNCHANGED ctl_vars



zkStatusToCtlPC ==
    IF zk_status = "WaitReplicate"
        THEN "CtlReadLeaderLog"
        ELSE IF zk_status = ""


CtlUpdateZKInfo ==
    /\ ctl_epoch < zk_epoch
    /\ ctl_epoch' = zk_epoch
    /\ ctl_leader' = zk_leader
    /\ ctl_pc' = IF zk_status = "WaitReplicate"
        THEN "CtlReadLeaderLog"
        ELSE "Init"
    /\ ctl_replicas' = zk_replicas
    /\ ctl_offset' = [r \in Replica |-> 0]
    /\ UNCHANGED global_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED zk_vars


CtlReadLeaderLog ==
    /\ ctl_pc = "CtlReadLeaderLog"
    /\ ctl_epoch = db_epoch[ctl_leader]
    /\ ctl_pc' = "CtlReadReplicaLog"
    /\ ctl_offset' = [ctl_offset EXCEPT ![ctl_leader] = Len(db[ctl_leader])]
    /\ UNCHANGED <<ctl_epoch, ctl_replicas, ctl_leader>>
    /\ UNCHANGED zk_vars
    /\ UNCHANGED global_vars
    /\ UNCHANGED db_vars


CtlReadReplicaLog(r) ==
    /\ ctl_pc = "CtlReadReplicaLog"
    /\ r /= ctl_leader
    /\ r \in ctl_replicas
    /\ ctl_offset[r] < Len(db[r])
    /\ ctl_offset' = [ctl_offset EXCEPT ![r] = Len(db[r])]
    /\ UNCHANGED <<ctl_pc, ctl_replicas>>
    /\ UNCHANGED <<ctl_epoch, ctl_leader>>
    /\ UNCHANGED zk_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED global_vars


CtlSetZkNormal ==
    /\ ctl_pc = "CtlReadReplicaLog"
    /\ ctl_epoch = zk_epoch
    /\ \E Q \in quorumOfSet(ctl_replicas):
        \A r \in Q: ctl_offset[r] >= ctl_offset[ctl_leader]
    /\ ctl_pc' = "Finished"
    /\ zk_status' = "Normal"
    /\ zk_epoch' = zk_epoch + 1
    /\ UNCHANGED <<zk_leader_epoch, zk_leader, zk_replicas>>
    /\ UNCHANGED <<ctl_epoch, ctl_leader, ctl_replicas, ctl_offset>>
    /\ UNCHANGED db_vars
    /\ UNCHANGED global_vars


Next ==
    \/ \E r \in Replica:
        \/ AppendLog(r)
        \/ AppendClientLog(r)
        \/ ZkAddReplica(r)
        \/ DBUpdateZKInfo(r)
        \/ DBReceveFromLeader(r)
        \/ \E r1 \in Replica: DBUpdateReplicated(r, r1)
        \/ CtlReadReplicaLog(r)
    \/ CtlUpdateZKInfo
    \/ CtlReadLeaderLog
    \/ CtlSetZkNormal
    \/ ZkPrepareChangeLeader
    \/ Terminated


Consistent ==
    /\ Len(db[zk_leader]) >= Len(client_log)
    /\ client_log = SubSeq(db[zk_leader], 1, Len(client_log))


Perms == Permutations(Replica)

====