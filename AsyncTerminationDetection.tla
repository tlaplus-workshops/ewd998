---------------------- MODULE AsyncTerminationDetection ---------------------
EXTENDS Naturals

CONSTANT N

ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLE active, network, terminationDetected

terminated ==
    \A n \in Node: active = {} /\ network[n] = 0

Init ==
    /\ active = Node
    /\ network = [ n \in Node |-> 0 ]
    /\ terminationDetected = terminated

TypeOK ==
    /\ active \in SUBSET Node
    /\ network \in [ Node -> Nat ]
    /\ terminationDetected \in BOOLEAN 

SendMsg(snd, rcv) ==
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]
    /\ snd \in active
    /\ active' = active
    /\ terminationDetected' = terminationDetected

RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ network' = [ network EXCEPT ![rcv] = @ - 1 ]
    /\ active' = active \cup {rcv}
    /\ terminationDetected' = terminationDetected

Idle(n) ==
    \* /\ n \in active
    /\ active' = active \ {n}
    /\ network' = network
    /\ terminationDetected' \in {terminationDetected, terminated'}
    \* /\ \/ terminationDetected' = terminationDetected
    \*    \/ terminationDetected' = terminated'

Next ==
    \E s,r \in Node:
        \/ SendMsg(s,r)
        \/ Idle(s)
        \/ RecvMsg(s)

Spec ==
    Init /\ [][Next]_<<active, network, terminationDetected>>

----

Safe ==
    \*IF terminationDetected THEN terminated ELSE TRUE
    [](terminationDetected => terminated)

\* Detect termination once (eventually) termination happens
Live ==
    [](terminated => <>terminationDetected)

----

Constraint ==
    \A rcv \in Node: network[rcv] < 3

=============================================================================