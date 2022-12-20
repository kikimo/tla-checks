----------------------------- MODULE FindMedian -----------------------------

EXTENDS TLC, Sequences, FiniteSets, Integers

VARIABLE matchIndex

Init ==
  /\ matchIndex = [ s \in {1, 2, 3, 4, 5} |-> s ]

RECURSIVE F2S(_, _)
F2S(F, S) == 
  IF Cardinality(S) = 0 THEN <<>> 
                        ELSE
                          LET
                            max == CHOOSE u \in S: \A v \in S: matchIndex[u] >= matchIndex[v] 
                          IN
                            <<matchIndex[max]>> \o F2S(F, S\{max})

FindMedian(F) ==
  LET
    mlist == F2S(F, DOMAIN F)
    pos == Len(mlist) \div 2 + 1
  IN
    mlist[pos]

Next == 
    /\ Print(FindMedian(matchIndex), TRUE)
    /\ UNCHANGED matchIndex

=============================================================================
\* Modification History
\* Last modified Tue Dec 20 23:04:12 CST 2022 by wenlinwu
\* Created Tue Dec 20 23:03:10 CST 2022 by wenlinwu
