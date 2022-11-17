---------------------- MODULE AsyncTerminationDetection ---------------------
EXTENDS Naturals

CONSTANT N
ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLE network, active, terminationDetected
vars == <<network, active, terminationDetected>> 

terminated == \A m \in Node: active[m] = FALSE /\ network[m] = 0

TypeOK ==
    \* /\ \A n \in Node: network[n] \in Nat
    \* /\ DOMAIN network = Node
    /\ network \in [ Node -> Nat ]
    /\ active \in [ Node -> BOOLEAN ]
    /\ terminationDetected \in BOOLEAN 

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network = [ n \in Node |-> 0 ] 
    /\ \/ terminationDetected = terminated
       \/ terminationDetected = FALSE
    \* /\ terminatedDetected \in {FALSE, terminated}

(*
    if (network[rcv] > 0) 
        active[rcv] := TRUE
        network[rcv]--
*)
RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ active' = [ active EXCEPT ![rcv] = TRUE ] 
    /\ network' = [ network EXCEPT ![rcv] = @ - 1 ]
    /\ UNCHANGED terminationDetected

(*
    active[n] := FALSE
*)
Terminate(n) ==
    /\ UNCHANGED network
    /\ active' = [ active EXCEPT ![n] = FALSE ]
    \* /\ terminationDetected' \in {terminationDetected, terminated'}
    /\ \/ terminationDetected' = terminated'
       \/ UNCHANGED terminationDetected

(*
    if (active[snd] > TRUE) 
        network[rcv]++
*)
SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ UNCHANGED active
    /\ UNCHANGED terminationDetected
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]

Next ==
    \E n,m \in Node:
        \/ Terminate(n)
        \/ RecvMsg(n)
        \/ SendMsg(n,m)

Spec ==
    Init /\ [][Next]_vars    \* [A]_v   <=>    A \/ v = v' 

Safe ==
    \*IF terminationDetected THEN terminated ELSE TRUE
    [](terminationDetected => terminated)

---------

Constraint ==
    \A n \in Node: network[n] < 3
=============================================================================

Live ==
    "Eventually" terminationDetected
