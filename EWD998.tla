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

---------------------- MODULE EWD998 ---------------------
EXTENDS Naturals

CONSTANT N
ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

black == "black"
white == "white"

Color == {black, white}

VARIABLE network, 
         active, color, counter,
         tokenPos, tokenCounter (* "q" *), tokenColor
vars == << network,active, color, counter,tokenPos, tokenCounter (* "q" *), tokenColor>>
tokenVar == << tokenPos, tokenColor, tokenCounter >>

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
    /\ counter = [ n \in Node |-> 0 ]

    /\ tokenCounter = 0
    /\ tokenColor = "white" \* ???
    /\ tokenPos = 0

PassToken ==
    /\ tokenPos # 0
    /\ tokenPos' = tokenPos - 1
    /\ TRUE

InitiateToken == 
    /\ tokenPos = 0
    /\ tokenPos' = N - 1
    /\ TRUE

(*
    if (network[rcv] > 0) 
        active[rcv] := TRUE
        network[rcv]--
*)
RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ active' = [ active EXCEPT ![rcv] = TRUE ] 
    /\ network' = [ network EXCEPT ![rcv] = @ - 1 ]
    /\ counter' = [ counter EXCEPT ![rcv] = @ - 1 ] 
    /\ UNCHANGED tokenVar

(*
    active[n] := FALSE
*)
Terminate(n) ==
    /\ UNCHANGED network
    /\ UNCHANGED tokenVar
    /\ active' = [ active EXCEPT ![n] = FALSE ]

(*
    if (active[snd] > TRUE) 
        network[rcv]++
*)
SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ UNCHANGED << tokenVar, active>>
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]
    /\ counter' = [ counter EXCEPT ![snd] = @ + 1 ]

Next ==
    \E n,m \in Node:
        \/ Terminate(n)
        \/ RecvMsg(n)
        \/ SendMsg(n,m)
        \/ TRUE \*TODO

Spec ==
    Init /\ [][Next]_vars

ATD == INSTANCE AsyncTerminationDetection
        \* TODO Refinement bogus!
       WITH terminationDetected <- TRUE

ATDSpec == ATD!Spec

Implements == 
    Spec => ATDSpec

---------

Constraint ==
    \A n \in Node: network[n] < 3
=============================================================================


Safe ==
    \*IF terminationDetected THEN terminated ELSE TRUE
    [](terminationDetected => terminated)

Live ==
    "Eventually" terminationDetected
