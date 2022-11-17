0) Sending a message by node  i  increments a counter at  i  , the receipt of a
   message decrements i's counter
3) Receiving a *message* (not token) blackens the (receiver) node
2) An active node j -owning the token- keeps the token.  When j becomes inactive,
   it passes the token to its neighbor with  q = q + counter[j] 
4) A black node taints the token
7) Passing the token whitens the sender node
1) The initiator sends the token with a counter  q  initialized to  0  and color
   white
5) The initiator starts a new round iff the current round is inconclusive
6) The initiator whitens itself and the token when initiating a new round

---------------------- MODULE AsyncTerminationDetection ---------------------
EXTENDS Naturals

CONSTANT N
ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1
Color == {"black", "white"}

VARIABLE network, 
         active, color, counter,
         tokenPos, tokenCounter, tokenColor

terminated == \A m \in Node: active[m] = FALSE /\ network[m] = 0

TypeOK ==
    \* /\ \A n \in Node: network[n] \in Nat
    \* /\ DOMAIN network = Node
    /\ network \in [ Node -> Nat ]
    /\ active \in [ Node -> BOOLEAN ]
    /\ color \in [ Node -> Color ]

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network = [ n \in Node |-> 0 ] 

PassToken ==
    TRUE

InitiateToken == 
    TRUE

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
