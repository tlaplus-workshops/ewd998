---------------------- MODULE AsyncTerminationDetection ---------------------
EXTENDS Naturals

CONSTANT N
ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLE network, active

terminated == \A m \in Node: active[m] = FALSE /\ network[m] = 0

TypeOK ==
    \* /\ \A n \in Node: network[n] \in Nat
    \* /\ DOMAIN network = Node
    /\ network \in [ Node -> Nat ]
    /\ active \in [ Node -> BOOLEAN ]

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network = [ n \in Node |-> 0 ] 

(*
    if (network[rcv] > 0) 
        active[rcv] := TRUE
        network[rcv]--
*)
RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ active' = [ active EXCEPT ![rcv] = TRUE ] 
    /\ network' = [ network EXCEPT ![rcv] = @ - 1 ]

(*
    active[n] := FALSE
*)
Terminate(n) ==
    /\ UNCHANGED network
    /\ active' = [ active EXCEPT ![n] = FALSE ]

(*
    if (active[snd] > TRUE) 
        network[rcv]++
*)
SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ UNCHANGED active
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]

Next ==
    \E n,m \in Node:
        \/ Terminate(n)
        \/ RecvMsg(n)
        \/ SendMsg(n,m)

---------

Constraint ==
    \A n \in Node: network[n] < 3
=============================================================================


Safe ==
    \*IF terminationDetected THEN terminated ELSE TRUE
    [](terminationDetected => terminated)

Live ==
    "Eventually" terminationDetected
