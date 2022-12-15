--------------------------- MODULE LeaderElection ---------------------------

EXTENDS Integers, FiniteSets, TLC

\* Constants definition
CONSTANT Servers

CONSTANT VoteReq, VoteResp

CONSTANT None

CONSTANT MaxTerm

CONSTANT Follower, Candidate, Leader

ASSUME /\ MaxTerm \in Nat
       /\ Servers # {}

\* Variables definition
VARIABLE votedFor

VARIABLE currentTerm

VARIABLE role

VARIABLE msgs


\* helpers
SendMsg(m) == msgs' = msgs \cup {m}

Init == /\ votedFor = [s \in Servers |-> None ]
        /\ currentTerm = [ s \in Servers |-> 0 ]
        /\ role = [ s \in Servers |-> Follower ]
        /\ msgs = {}

BecomeCandidate(s) == /\ currentTerm[s] + 1 <= MaxTerm
                      /\ role[s] = Follower
                      /\ currentTerm' = [ currentTerm EXCEPT ![s] = currentTerm[s] + 1 ]
                      /\ role' = [ role EXCEPT ![s] = Candidate ]
                      /\ votedFor' = [ votedFor EXCEPT ![s] = s ]
                      /\ UNCHANGED msgs

RequestVote(s) == /\ role[s] = Candidate
                  /\ \E dst \in Servers\{s}:
                       /\ ~ \E m \in msgs:
                              /\ m.dst = dst
                              /\ m.src = s
                              /\ m.term = currentTerm[s]
                              /\ m.type = VoteReq
                       /\ SendMsg([ dst |-> dst, src |-> s, term |-> currentTerm[s], type |-> VoteReq ])
                  /\ UNCHANGED <<votedFor, currentTerm, role>>

ResponseVote(s) == /\ \E m \in msgs:
                        /\ m.dst = s
                        /\ m.type = VoteReq
                        /\ \/ currentTerm[s] < m.term
                           \/ currentTerm[s] = m.term /\ votedFor[s] = None
                        /\ SendMsg([ dst |-> m.src, src |-> s, term |-> m.term, type |-> VoteResp ])
                        /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
                        /\ votedFor' = [ votedFor EXCEPT ![s] = m.src ]
                   /\ role' = [ role EXCEPT ![s] = Follower ]

BecomeLeader(s) == /\ role[s] = Candidate
                   /\ LET
                        resps == {m \in msgs : /\ m.dst = s
                                               /\ m.term = currentTerm[s]
                                               /\ m.type = VoteResp }
                      IN
                        /\ (Cardinality(resps) + 1) * 2 > Cardinality(Servers)
                        /\ role' = [ role EXCEPT ![s] = Leader ]
                        \* /\ Print(resps, TRUE)
                        \* /\ Print({role', currentTerm, votedFor}, TRUE)
                        /\ UNCHANGED <<currentTerm, votedFor, msgs>>

Next == \E s \in Servers:
          \/ BecomeCandidate(s)
          \/ RequestVote(s)
          \/ ResponseVote(s)
          \/ BecomeLeader(s)

\* Invariants
NoSplitVote == /\ ~ \E s1, s2 \in Servers:
                     /\ s1 # s2
                     /\ currentTerm[s1] = currentTerm[s2]
                     /\ role[s1] = Leader
                     /\ role[s2] = Leader
                     \* /\ Print({currentTerm, role, votedFor}, TRUE)

=============================================================================
\* Modification History
\* Last modified Wed Dec 14 23:23:29 CST 2022 by wenlinwu
\* Created Wed Dec 14 10:07:36 CST 2022 by wenlinwu
