------ MODULE SemiSync ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Replica, nil

VARIABLES
    next_req,
    db, db_leader, db_epoch, db_leader_epoch,
    db_replicas, db_replicated,
    zk_leader, zk_epoch, zk_leader_epoch,
    zk_replicas, zk_status, zk_deleted, zk_num_change,
    zk_num_remove,
    ctl_pc, ctl_epoch, ctl_leader, ctl_replicas, ctl_offset,
    client_log

zk_vars == <<zk_leader, zk_epoch, zk_leader_epoch,
    zk_replicas, zk_status, zk_deleted, zk_num_change, zk_num_remove>>
db_vars == <<db, db_leader, db_epoch, db_leader_epoch, db_replicas, db_replicated>>
ctl_vars == <<ctl_pc, ctl_epoch, ctl_leader, ctl_replicas, ctl_offset>>
global_vars == <<next_req, client_log>>

vars == <<global_vars, db_vars, zk_vars, ctl_vars>>

LogEntry == 41..50
EpochNumber == 11..30

NullLogEntry == LogEntry \union {nil}
NullReplica == Replica \union {nil}

max_req == 40 + 2
max_change_leader == 2
max_remove_replica == 2


replicationFactor(n) == (n + 2) \div 2

quorumOfSet(S) ==
    {Q \in SUBSET S: Cardinality(Q) = replicationFactor(Cardinality(S))}

quorumOf(r) == quorumOfSet(db_replicas[r])


\* ================================================
\* Map Functions
\* ================================================

Range(f) == {f[x]: x \in DOMAIN f}

mapPut(f, k, v) == LET newDomain == (DOMAIN f) \union {k} IN
    /\ f' = [x \in newDomain |-> IF x = k THEN v ELSE f[x]]

mapExist(f, k) == k \in DOMAIN f

mapDelete(f, k) == LET newDomain == (DOMAIN f) \ {k} IN
    /\ f' = [x \in newDomain |-> f[x]]

MapOf(f, K, V) ==
    /\ DOMAIN f \subseteq K
    /\ Range(f) \subseteq V


TypeOK ==
    /\ next_req \in LogEntry \union {40}

    /\ zk_leader \in NullReplica
    /\ zk_epoch \in EpochNumber
    /\ zk_leader_epoch \in EpochNumber
    /\ zk_replicas \subseteq Replica
    /\ zk_status \in {"Normal", "WaitReplicate", "FindNewLeader"}
    /\ MapOf(zk_deleted, Replica, 0..10)
    /\ zk_num_change \in 0..20
    /\ zk_num_remove \in 0..20

    /\ zk_leader /= nil => (zk_leader \in zk_replicas)

    /\ db \in [Replica -> Seq(LogEntry)]
    /\ db_leader \in [Replica -> NullReplica]
    /\ db_epoch \in [Replica -> EpochNumber]
    /\ db_leader_epoch \in [Replica -> EpochNumber]
    /\ db_replicas \in [Replica -> SUBSET Replica]
    /\ db_replicated \in [Replica -> [Replica -> 0..10]]

    /\ ctl_pc \in {
        "Init", "CtlReadLeaderLog", "CtlReadReplicaLog",
        "CtlFindNewLeader"}
    /\ ctl_epoch \in EpochNumber
    /\ ctl_leader \in NullReplica
    /\ ctl_replicas \subseteq Replica
    /\ ctl_offset \in [Replica -> 0..10 \union {-1}]

    /\ client_log \in Seq(LogEntry)


Init ==
    /\ next_req = 40

    /\ zk_leader \in Replica
    /\ zk_epoch = 11
    /\ zk_leader_epoch = zk_epoch
    /\ zk_replicas = {zk_leader}
    /\ zk_status = "Normal"
    /\ zk_deleted = <<>>
    /\ zk_num_change = 0
    /\ zk_num_remove = 0

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
    /\ ~(r \in DOMAIN zk_deleted)
    /\ zk_status = "Normal" \/ zk_status = "WaitReplicate"
    /\ zk_replicas' = zk_replicas \union {r}
    /\ zk_epoch' = zk_epoch + 1
    /\ zk_status' = "WaitReplicate"
    /\ UNCHANGED <<zk_leader, zk_leader_epoch, zk_deleted, zk_num_change>>
    /\ UNCHANGED zk_num_remove
    /\ UNCHANGED global_vars
    /\ UNCHANGED db_vars
    /\ UNCHANGED ctl_vars


ZkRemoveReplica(r) ==
    /\ zk_num_remove < max_remove_replica
    /\ zk_num_remove' = zk_num_remove + 1

    /\ r \in zk_replicas
    /\ r /= zk_leader
    /\ zk_status = "Normal" \* TODO Remove
    /\ zk_epoch' = zk_epoch + 1
    /\ zk_replicas' = zk_replicas \ {r}
    /\ IF Cardinality(zk_replicas') = 1
        THEN /\ zk_status = "Normal"
             /\ UNCHANGED zk_deleted
        ELSE /\ zk_status = "WaitReplicate"
             /\ mapPut(zk_deleted, r, Len(db[zk_leader]))
    /\ UNCHANGED <<zk_leader, zk_leader_epoch, zk_status>>
    /\ UNCHANGED zk_num_change
    /\ UNCHANGED db_vars
    /\ UNCHANGED global_vars
    /\ UNCHANGED ctl_vars


ZkPrepareChangeLeader ==
    /\ zk_num_change < max_change_leader
    /\ zk_num_change' = zk_num_change + 1

    /\ Cardinality(zk_replicas) > 1
    /\ zk_status = "Normal"
    /\ zk_replicas' = zk_replicas \ {zk_leader}
    /\ \E r2 \in zk_replicas':
        /\ mapPut(zk_deleted, zk_leader, Len(db[r2]))
    /\ zk_epoch' = zk_epoch + 1
    /\ IF Cardinality(zk_replicas') > 1
        THEN /\ zk_status' = "FindNewLeader"
             /\ zk_leader' = nil
             /\ UNCHANGED <<zk_leader_epoch>>
        ELSE /\ UNCHANGED zk_status
             /\ zk_leader' \in zk_replicas'
             /\ zk_leader_epoch' = zk_epoch'
    /\ UNCHANGED zk_num_remove
    /\ UNCHANGED db_vars
    /\ UNCHANGED global_vars
    /\ UNCHANGED ctl_vars


newReplicated == [r \in Replica |-> 0]

DBUpdateZKInfo(r) ==
    /\ db_epoch[r] < zk_epoch
    /\ db_epoch' = [db_epoch EXCEPT ![r] = zk_epoch]
    /\ db_leader_epoch' = [db_leader_epoch EXCEPT ![r] = zk_leader_epoch]
    /\ db_leader' = [db_leader EXCEPT ![r] = zk_leader]
    /\ db_replicas' = [db_replicas EXCEPT ![r] = zk_replicas]
    /\ IF zk_leader_epoch = db_leader_epoch[r]
        THEN UNCHANGED db_replicated
        ELSE db_replicated' = [
            db_replicated EXCEPT ![r] = [newReplicated EXCEPT ![r] = Len(db[r])]]
    /\ UNCHANGED db
    /\ UNCHANGED zk_vars
    /\ UNCHANGED global_vars
    /\ UNCHANGED ctl_vars


DBReceveFromLeader(r) == LET leader == db_leader[r] IN
    /\ leader /= r
    /\ leader /= nil
    /\ r \in db_replicas[r]
    /\ r \in db_replicas[leader]
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
    /\ r1 \in db_replicas[r1]
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
        ELSE IF zk_status = "FindNewLeader"
            THEN "CtlFindNewLeader"
            ELSE "Init"


initCtlOffset == ctl_offset' = [r \in Replica |-> -1]

CtlUpdateZKInfo ==
    /\ ctl_epoch < zk_epoch
    /\ ctl_epoch' = zk_epoch
    /\ ctl_leader' = zk_leader
    /\ ctl_pc' = zkStatusToCtlPC
    /\ ctl_replicas' = zk_replicas
    /\ initCtlOffset
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

    /\ zk_status' = "Normal"
    /\ zk_epoch' = zk_epoch + 1
    /\ UNCHANGED <<zk_leader_epoch, zk_leader, zk_replicas, zk_deleted>>
    /\ UNCHANGED <<zk_num_change, zk_num_remove>>

    /\ ctl_pc' = "Init"
    /\ ctl_epoch' = zk_epoch'
    /\ initCtlOffset
    /\ UNCHANGED <<ctl_leader, ctl_replicas>>

    /\ UNCHANGED db_vars
    /\ UNCHANGED global_vars


CtlFindNewLeader(r) ==
    /\ ctl_pc = "CtlFindNewLeader"
    /\ r \in ctl_replicas
    /\ db_epoch[r] = ctl_epoch
    /\ ctl_offset[r] < Len(db[r])
    /\ ctl_offset' = [ctl_offset EXCEPT ![r] = Len(db[r])]
    /\ UNCHANGED <<ctl_epoch, ctl_leader, ctl_pc, ctl_replicas>>
    /\ UNCHANGED zk_vars
    /\ UNCHANGED global_vars
    /\ UNCHANGED db_vars


CtlSetNewLeader(r) ==
    /\ ctl_pc = "CtlFindNewLeader"
    /\ r \in ctl_replicas
    /\ zk_epoch = ctl_epoch
    /\ \E Q \in quorumOfSet(ctl_replicas):
        /\ r \in Q
        /\ \A r1 \in Q:
            /\ ctl_offset[r1] >= 0
            /\ ctl_offset[r] >= ctl_offset[r1]
    /\ zk_epoch' = zk_epoch + 1
    /\ zk_leader' = r
    /\ zk_leader_epoch' = zk_epoch'

    /\ ctl_epoch' = zk_epoch'
    /\ ctl_leader' = zk_leader'
    /\ initCtlOffset

    /\ zk_status' = "WaitReplicate"
    /\ ctl_pc' = "CtlReadLeaderLog"

    /\ UNCHANGED ctl_replicas
    /\ UNCHANGED <<zk_replicas, zk_deleted, zk_num_change, zk_num_remove>>
    /\ UNCHANGED db_vars
    /\ UNCHANGED global_vars



subSeqMin(S, n) ==
    IF Len(S) < n
        THEN S
        ELSE SubSeq(S, 1, n)

TruncateDeletedDB(r) ==
    /\ r \in DOMAIN zk_deleted
    /\ db_epoch[r] = zk_epoch
    /\ mapDelete(zk_deleted, r)
    /\ zk_epoch' = zk_epoch + 1
    /\ db' = [db EXCEPT ![r] = subSeqMin(@, zk_deleted[r])]
    /\ UNCHANGED <<db_epoch, db_leader, db_leader_epoch, db_replicas, db_replicated>>
    /\ UNCHANGED <<zk_leader, zk_leader_epoch, zk_replicas, zk_status>>
    /\ UNCHANGED <<zk_num_change, zk_num_remove>>
    /\ UNCHANGED ctl_vars
    /\ UNCHANGED global_vars


TerminateCond ==
    /\ next_req = max_req
    /\ zk_num_change = max_change_leader
    /\ zk_replicas = Replica
    /\ zk_leader /= nil
    /\ Len(client_log) = Len(db[zk_leader])
    /\ zk_status = "Normal"

Terminated ==
    /\ TerminateCond
    /\ UNCHANGED vars


Next ==
    \/ \E r \in Replica:
        \/ AppendLog(r)
        \/ AppendClientLog(r)
        \/ ZkAddReplica(r)
        \/ ZkRemoveReplica(r)
        \/ DBUpdateZKInfo(r)
        \/ DBReceveFromLeader(r)
        \/ \E r1 \in Replica: DBUpdateReplicated(r, r1)
        \/ CtlReadReplicaLog(r)
        \/ CtlFindNewLeader(r)
        \/ CtlSetNewLeader(r)
        \/ TruncateDeletedDB(r)
    \/ CtlUpdateZKInfo
    \/ CtlReadLeaderLog
    \/ CtlSetZkNormal
    \/ ZkPrepareChangeLeader
    \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

AlwaysFinish == <> TerminateCond

CanRecvReqAfterFailed ==
    /\ zk_num_change = max_change_leader
    /\ zk_replicas = Replica
    /\ zk_status = "Normal"
    /\ next_req = 40
    ~> client_log = <<41, 42>>


ConsistentWhenLeaderValid ==
    /\ Len(db[zk_leader]) >= Len(client_log)
    /\ client_log = SubSeq(db[zk_leader], 1, Len(client_log))
    
Consistent ==
    /\ zk_leader /= nil => ConsistentWhenLeaderValid
    /\ zk_status = "Normal" => zk_leader /= nil
    /\ \A r \in DOMAIN zk_deleted: ~(r \in zk_replicas)
    \* /\ TerminateCond => client_log /= <<41, 42>> \* Couter Condition


Perms == Permutations(Replica)

====