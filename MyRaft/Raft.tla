--------------------------- MODULE Raft ---------------------------

EXTENDS Integers, FiniteSets, Sequences, TLC

\* Constants definition
CONSTANT Servers

CONSTANT VoteReq, VoteResp, AppendReq, AppendResp

CONSTANT None

CONSTANT MaxTerm, MaxLogSize

CONSTANT Follower, Candidate, Leader

ASSUME /\ MaxTerm \in Nat
       /\ Servers # {}

\* Variables definition
VARIABLE votedFor

VARIABLE currentTerm

VARIABLE role

VARIABLE msgs

\* transient state variables
VARIABLE matchIndex

VARIABLE nextIndex

VARIABLE commitIndex

VARIABLE logs

Indexes == <<matchIndex, nextIndex, commitIndex>>

\* helpers
SendMsg(m) == msgs' = msgs \cup {m}

Min(a, b) == IF a < b THEN a ELSE b

Init == /\ votedFor = [s \in Servers |-> None ]
        /\ currentTerm = [ s \in Servers |-> 0 ]
        /\ role = [ s \in Servers |-> Follower ]
        /\ logs = [ s \in Servers |-> <<[term |-> 0, val |-> None]>> ]
        /\ matchIndex = [ s \in Servers |-> [ t \in Servers |-> 1 ] ]
        /\ nextIndex = [ s \in Servers |-> [ t \in Servers |-> 2 ] ]
        /\ commitIndex = [ s \in Servers |-> 1 ]
        /\ msgs = {}

BecomeCandidate(s) == /\ currentTerm[s] + 1 <= MaxTerm
                      /\ role[s] = Follower
                      /\ currentTerm' = [ currentTerm EXCEPT ![s] = currentTerm[s] + 1 ]
                      /\ role' = [ role EXCEPT ![s] = Candidate ]
                      /\ votedFor' = [ votedFor EXCEPT ![s] = s ]
                      /\ UNCHANGED <<msgs, logs, Indexes>>

RequestVote(s) == /\ role[s] = Candidate
                  /\ \E dst \in Servers\{s}:
                       LET
                         m == [ dst |-> dst, src |-> s, term |-> currentTerm[s], type |-> VoteReq ]
                       IN
                         /\ m \notin msgs
                         /\ SendMsg(m)
                         /\ UNCHANGED <<votedFor, currentTerm, role, logs, Indexes>>

ResponseVote(s) == /\ role[s] = Follower
                   /\ \E m \in msgs:
                        /\ m.dst = s
                        /\ m.type = VoteReq
                        /\ m.term = currentTerm[s]
                        /\ votedFor[s] = None
                        /\ LET
                             gm == [ dst |-> m.src, src |-> s, term |-> m.term, type |-> VoteResp ]
                           IN
                             /\ gm \notin msgs
                             /\ SendMsg(gm)
                             /\ votedFor' = [ votedFor EXCEPT ![s] = m.src ]
                             /\ UNCHANGED <<currentTerm, role, logs, Indexes>>

BecomeLeader(s) == /\ role[s] = Candidate
                   /\ LET
                        resps == {m \in msgs : /\ m.dst = s
                                               /\ m.term = currentTerm[s]
                                               /\ m.type = VoteResp }
                      IN
                        /\ (Cardinality(resps) + 1) * 2 > Cardinality(Servers)
                        /\ role' = [ role EXCEPT ![s] = Leader ]
                        /\ matchIndex' = [ matchIndex EXCEPT ![s] = [ u \in Servers |-> 1 ] ]
                        /\ nextIndex' = [ nextIndex EXCEPT ![s] = [ u \in Servers |-> Len(logs[s])+1 ] ]
                        \* /\ Print(resps, TRUE)
                        \* /\ Print({role', currentTerm, votedFor}, TRUE)
                        /\ UNCHANGED <<currentTerm, votedFor, msgs, logs, commitIndex>>


FollowerUpdateTerm(s) == /\ role[s] = Follower
                         /\ \E m \in msgs:
                              /\ m.term > currentTerm[s]
                              /\ m.dst = s
                              /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
                              /\ UNCHANGED <<votedFor, msgs, role, logs, Indexes>>

CandateToFollower(s) == /\ role[s] = Candidate
                        /\ \E m \in msgs:
                             \/ /\ m.term > currentTerm[s]
                                /\ m.dst = s
                                /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
                                /\ role' = [ role EXCEPT ![s] = Follower ]
                                /\ votedFor' = [ votedFor EXCEPT ![s] = None ]
                                /\ UNCHANGED <<msgs, logs, Indexes>>
                             \/ /\ m.term = currentTerm[s]
                                /\ m.dst = s
                                /\ m.type = AppendReq
                                /\ role' = [ role EXCEPT ![s] = Follower ]
                                /\ UNCHANGED <<votedFor, currentTerm, msgs, logs, Indexes>>

LeaderToFollower(s) == /\ role[s] = Leader
                       /\ \E m \in msgs:
                            /\ m.term > currentTerm[s]
                            /\ m.dst = s
                            /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
                            /\ role' = [ role EXCEPT ![s] = Follower ]
                            /\ votedFor' = [ votedFor EXCEPT ![s] = None ]
                            /\ UNCHANGED <<msgs, logs, Indexes>>

BecomeFollower(s) == \/ FollowerUpdateTerm(s)
                     \/ CandateToFollower(s)
                     \/ LeaderToFollower(s)

ClientReq(s) == /\ role[s] = Leader
                /\ Len(logs[s]) <= MaxLogSize
                /\ logs' = [ logs EXCEPT ![s] = Append(logs[s], [ term |-> currentTerm[s], val |-> None ]) ]
                /\ UNCHANGED <<currentTerm, votedFor, msgs, role, Indexes>>

LeaderAppendEntry(s) == /\ role[s] = Leader
                  /\ \E dst \in Servers:
                       /\ dst # s
                       /\ nextIndex[s][dst] < Len(logs[s])
                       /\ LET
                           prevLogIndex == nextIndex[s][dst] - 1
                           prevLogTerm == logs[s][prevLogIndex].term
                           \* send only one entry at a time
                           m == [
                                    type |-> AppendReq,
                                    dst |-> dst,
                                    src |-> s,
                                    prevLogIndex |-> prevLogIndex,
                                    prevLogTerm |-> prevLogTerm,
                                    term |-> currentTerm[s],
                                    entry |-> logs[s][prevLogIndex+1]
                                ]
                         IN
                           /\ m \notin msgs
                           /\ SendMsg(m)
                           /\ UNCHANGED <<Indexes, currentTerm, votedFor, role, logs>>

IsLogMatch(s, m) ==
  /\ m.prevLogIndex <= Len(logs[s]) 
  /\ m.prevLogTerm = logs[s][m.prevLogIndex].term

MakeAppendResp(s, m) ==
  IF IsLogMatch(s, m) THEN
    [type |-> AppendResp, dst |-> m.src, src |-> s, prevLogIndex |-> m.prevLogIndex, succ |-> TRUE, term |-> m.term]
  ELSE 
    [type |-> AppendResp, dst |-> m.src, src |-> s, prevLogIndex |-> m.prevLogIndex - 1, succ |-> FALSE, term |-> m.term]

FollowerAppendEntry(s) == 
  /\ role[s] = Follower
  /\ \E m \in msgs:
       /\ m.dst = s
       /\ m.term = currentTerm[s]
       /\ m.type = AppendReq
       /\ LET
            resp == MakeAppendResp(s, m)
          IN
            /\ resp \notin msgs
            /\ SendMsg(resp)
            /\ logs' = [ logs EXCEPT ![s] = Append(SubSeq(logs[s], 1, m.prevLogIndex), m.entry) ]
            /\ UNCHANGED <<Indexes, currentTerm, votedFor, role>>

\*CanCommit(s) == 
\*  LET
\*    mlist == <<>>
\*    pos == (Cardinality(Servers) / 2) + 1
\*  IN
\*    /\ \A e \in DOMAIN matchIndex: Append(mlist, matchIndex[e])
\*    /\ SortSeq(mlist, >)[pos] > commitIndex[s]
\*   

HandleAppendResp(s) ==
  /\ role[s] = Leader
  /\ \E m \in msgs:
    /\ m.type = AppendResp
    /\ m.dst = s
    /\ m.term = currentTerm[s]
    /\ IF m.succ THEN
         /\ matchIndex[s][m.src] < m.prevLogIndex + 1
         /\ matchIndex' = [ matchIndex EXCEPT ![s][m.src] = m.prevLogIndex + 1 ]
         /\ nextIndex' = [ nextIndex EXCEPT ![s][m.src] = m.prevLogIndex + 2 ]
         \* TODO commit entry if possible
         /\ UNCHANGED <<currentTerm, votedFor, role, msgs, commitIndex, logs>>
       ELSE
         \* enabling condition
         /\ m.prevLogIndex + 1 = nextIndex[s][m.src] - 1
         /\ Assert(m.prevLogIndex + 1 > matchIndex[s][m.src], "illegal nextIndex status")
         /\ nextIndex' = [ nextIndex EXCEPT ![s][m.src] = m.prevLogIndex + 1 ]
         /\ UNCHANGED <<currentTerm, votedFor, role, msgs, commitIndex, matchIndex, logs>>

Next == \E s \in Servers:
          \/ BecomeCandidate(s)
          \/ BecomeFollower(s)
          \/ RequestVote(s)
          \/ ResponseVote(s)
          \/ BecomeLeader(s)
          \/ ClientReq(s)
          \/ LeaderAppendEntry(s)
          \/ FollowerAppendEntry(s)
          \/ HandleAppendResp(s)

\* Invariants
NoSplitVote == ~ \E s1, s2 \in Servers:
                     /\ s1 # s2
                     /\ currentTerm[s1] = currentTerm[s2]
                     /\ role[s1] = Leader
                     /\ role[s2] = Leader
                     \* /\ Print({currentTerm, role, votedFor}, TRUE)

\* any better way?
NoLogDivergence == ~ \E s1, s2 \in Servers:
                       /\ s1 # s2
                       /\ LET
                            sz == Min(commitIndex[s1], commitIndex[s2])
                          IN
                            /\ SubSeq(logs[s1], 1, sz) # SubSeq(logs[s2], 1, sz)

=============================================================================
\* Modification History
\* Last modified Tue Dec 20 23:06:10 CST 2022 by wenlinwu
\* Created Wed Dec 14 10:07:36 CST 2022 by wenlinwu