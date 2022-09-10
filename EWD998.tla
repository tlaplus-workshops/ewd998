---------------------- MODULE EWD998 ---------------------
EXTENDS Integers, TLC

CONSTANT N

ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLE 
    active, 
    counter, 
    
    network,

    token

terminated ==
    \A n \in Node: active = {} /\ network[n] = 0

terminationDetected == 
    /\ token.pos = 0 
    /\ token.q + counter[0] = 0
    /\ token.color = "black"
    /\ 0 \notin active

Init ==
    /\ active = Node
    /\ counter = [ n \in Node |-> 0 ]
    /\ network = [ n \in Node |-> 0 ]
    /\ token = [ pos |-> 0, q |-> 0, color |-> "white" ]

TypeOK ==
    /\ active \in SUBSET Node
    /\ counter \in [ Node -> Int ]
    /\ network \in [ Node -> Nat ]
    /\ token \in [ pos: Node, q: Int, color: {"black", "white"} ]

Inv ==
    TLCGet("level") < 25

InitiateToken ==
    /\ ~terminationDetected
    /\ token.pos = 0
    /\ token' = [ token EXCEPT !.pos = N - 1, !.q = 0, !.color= "black" ]
    /\ UNCHANGED <<counter, active, network>>

PassToken ==
    /\ token.pos # 0
    /\ token.pos \notin active 
    /\ token' = [ token EXCEPT !.pos = @ - 1, !.q = @ + counter[token.pos] ]
    /\ UNCHANGED <<counter, active, network>>

SendMsg(snd, rcv) ==
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]
    /\ snd \in active
    /\ counter' = [ counter EXCEPT ![snd] = @ + 1]
    /\ UNCHANGED <<token, active>>

RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ network' = [ network EXCEPT ![rcv] = @ - 1 ]
    /\ active' = active \cup {rcv}
    /\ counter' = [ counter EXCEPT ![rcv] = @ - 1]
    /\ UNCHANGED <<token>>

Idle(n) ==
    \* /\ n \in active
    /\ active' = active \ {n}
    /\ UNCHANGED <<network, token, counter>>

Next ==
    \E s,r \in Node:
        \/ PassToken
        \/ InitiateToken
        \/ SendMsg(s,r)
        \/ Idle(s)
        \/ RecvMsg(s)

ATD == INSTANCE AsyncTerminationDetection

ATDSpec == ATD!Spec
----

\* Safe ==
\*     \*IF terminationDetected THEN terminated ELSE TRUE
\*     [](terminationDetected => terminated)

\* \* Detect termination once (eventually) termination happens
\* Live ==
\*     [](terminated => <>terminationDetected)

----

Constraint ==
    \A rcv \in Node: counter[rcv] \in -3..3

=============================================================================