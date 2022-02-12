---------------------- MODULE AsyncTerminationDetection ---------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NIsPosNat == N \in Nat \ {0} 

Node == 0 .. N-1                           \* == pp'ed as ≜

VARIABLE 
    active,
    pending,
    terminationDetected
vars == <<active, pending, terminationDetected>>

terminated ==
    \A n \in Node: active[n] = FALSE /\ pending[n] = 0

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> Nat ]
    /\ terminationDetected \in BOOLEAN 

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> Nat ]
    /\ terminationDetected \in {FALSE, terminated}

Terminate(n) ==
    /\ active' = [ active EXCEPT ![n] = FALSE ]
    /\ UNCHANGED pending
    /\ terminationDetected' \in {terminationDetected, terminated'}

SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ pending' = [ pending EXCEPT ![rcv] =  @ + 1 ]
    /\ pending' = [ pending EXCEPT ![rcv] =  pending[rcv] + 1 ]
    /\ UNCHANGED active
    /\ UNCHANGED terminationDetected
    
Wakeup(n) ==
    /\ pending[n] > 0
    /\ pending' = [ pending EXCEPT ![n] =  @ - 1 ]
    /\ active' = [ active EXCEPT ![n] = TRUE ]
    /\ UNCHANGED terminationDetected

DetectTermination ==
    /\ terminated
    /\ terminationDetected' = TRUE
    /\ UNCHANGED active
    /\ UNCHANGED pending

Next ==
    \E n,m \in Node:
        \/ Terminate(n)
        \/ SendMsg(n,m)
        \/ Wakeup(n)
        \/ DetectTermination

Spec ==
    Init /\ [][Next]_vars

Safe ==
    \* Only detect termination if the system has terminated.
    [](terminationDetected => terminated)

THEOREM Spec => Safe
=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl