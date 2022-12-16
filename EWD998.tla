Rules copied from top of
https://github.com/tlaplus-workshops/ewd998/blob/main/EWD998.tla

Let q  equal  tokenCounter

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
\* * TLA+ is an expressive language and we usually define operators on-the-fly.
 \* * That said, the TLA+ reference guide "Specifying Systems" (download from:
 \* * https://lamport.azurewebsites.net/tla/book.html) defines a handful of
 \* * standard modules.  Additionally, a community-driven repository has been
 \* * collecting more modules (http://modules.tlapl.us). In our spec, we are
 \* * going to need operators for natural numbers.
EXTENDS Naturals, Integers

\* * A constant is a parameter of a specification. In other words, it is a
 \* * "variable" that cannot change throughout a behavior, i.e., a sequence
 \* * of states. Below, we declares N to be a constant of this spec.
 \* * We don't know what value N has or even what its type is; TLA+ is untyped and
 \* * everything is a set. In fact, even 23 and "frob" are sets and 23="frob" is 
 \* * syntactically correct.  However, we don't know what elements are in the sets 
 \* * 23 and "frob" (nor do we care). The value of 23="frob" is undefined, and TLA+
 \* * users call this a "silly expression".
CONSTANT N

\* * We should declare what we assume about the parameters of a spec--the constants.
 \* * In this spec, we assume constant N to be a (positive) natural number, by
 \* * stating that N is in the set of Nat (defined in Naturals.tla) without 0 (zero).
 \* * Note that the TLC model-checker, which we will meet later, checks assumptions
 \* * upon startup.
ASSUME NIsPosNat == N \in Nat \ {0}

\* * A definition Id == exp defines Id to be synonymous with an expression exp.
 \* * A definition just gives a name to an expression. The name isn't special.
 \* * It is best to write comments that explain what is being defined. To get
 \* * a feeling for how extensive comments tend to be, see the Paxos spec at
 \* * https://git.io/JZJaD .
 \* * Here, we define Node to be synonymous with the set of naturals numbers
 \* * 0 to N-1.  Semantically, Node is going to represent the ring of nodes.
 \* * Note that the definition Node is a zero-arity (parameter-less) operator.
Node == 0 .. N-1                           \* == pp'ed as ≜

Initiator == 0

Color == { "white", "black" }

VARIABLE
    active,
    counter,
    \* Why color???
    color,

    network, 
    
    tokenPosition,
    tokenCounter,
    tokenColor

vars ==<<active, counter, color, network, tokenPosition, tokenCounter, tokenColor>>

terminated ==
    \A n \in Node: ~ active[n] /\ network[n] = 0

terminationDetected ==
    /\ tokenPosition = 0
    /\ counter[tokenPosition] + tokenCounter = 0
    /\ tokenColor = "white"
    /\ color[tokenPosition] = "white"
    /\ active[tokenPosition] = FALSE
    \* /\ terminated

Init ==
    /\ network \in [ Node -> 0..0 ]
    /\ active \in [ Node -> BOOLEAN ]
    /\ color \in [ Node -> Color ]
    /\ counter \in [ Node -> 0..0 ]
    /\ tokenPosition \in Node
    \* ???
    /\ tokenColor = "black"
    /\ tokenCounter = 0

InitiateToken ==
    /\ tokenPosition = 0
    /\ tokenPosition' = N - 1
    /\ tokenCounter' = 0
    /\ tokenColor' = "white"
    /\ color' = [ color EXCEPT ![0] = "white" ]
    /\ UNCHANGED <<active, counter, network>>

PassToken ==
    \* Pass the token to the neighbor.
    /\ active[tokenPosition] = FALSE
    /\ tokenPosition # 0
    /\ tokenPosition' = tokenPosition - 1
    /\ tokenCounter' = tokenCounter + counter[tokenPosition]
    /\ tokenColor' = IF color[tokenPosition] = "black" THEN "black" ELSE tokenColor
    \* /\ color' = [ color EXCEPT ![tokenPosition] = "white" ]
    /\ UNCHANGED color
    /\ UNCHANGED <<active, counter, network>>

SendMsg(snd, rcv) ==
    \* /\ network[rcv]++
    /\ network' = [ n \in Node |-> IF n = rcv THEN network[n] + 1 ELSE network[n] ]
    /\ counter' = [ n \in Node |-> IF n = snd THEN counter[n] + 1 ELSE counter[n] ] 
    /\ UNCHANGED active
    \* ??? Sender becomes active ???
    /\ active[snd] = TRUE
    /\ UNCHANGED <<tokenPosition, tokenCounter, tokenColor, color>>

RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ network' = [ n \in Node |-> IF n = rcv THEN network[n] - 1 ELSE network[n] ]
    /\ counter' = [ n \in Node |-> IF n = rcv THEN counter[n] - 1 ELSE counter[n] ] 
    /\ active' = [ n \in Node |-> IF n = rcv THEN TRUE ELSE active[n] ]
    /\ color' = [ n \in Node |-> IF n = rcv THEN "black" ELSE color[n] ]
    /\ UNCHANGED <<tokenPosition, tokenCounter, tokenColor>>

Idle(m) ==
    \* ??? Should we check network for empty? 
    /\ active' = [ n \in Node |-> IF n = m THEN FALSE ELSE active[n] ]
    /\ UNCHANGED network
    /\ UNCHANGED <<tokenPosition, tokenCounter, tokenColor, color, counter>>
       
Next ==
    \E n,m \in Node:
        \/ PassToken
        \/ InitiateToken 
        \/ Idle(n)
        \/ RecvMsg(n)
        \/ SendMsg(n,m)

Spec == Init /\ [][Next]_vars                  \*/\ WF_vars(Next)

ATD == INSTANCE AsyncTerminationDetection
ATDSpec == ATD!Spec

Implements == Spec => ATD!Spec
---------------------

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> Nat ]
    /\ counter \in [ Node -> Int ]
    /\ color \in [ Node -> Color ]
    /\ tokenPosition \in Node
    /\ tokenCounter \in Int
    /\ tokenColor \in Color
---------------------


Constraint ==
    \A n \in Node: network[n] < 3 /\ counter[n] \in -3..3 /\ tokenCounter \in -3..3


======



Safe ==
    \* If we detect termination, there is termination.
    \* IF terminationDetected THEN terminated ELSE TRUE
    terminationDetected => terminated

Live  ==
    \* Eventually detect termination.
    \* "Eventually" terminationDetected
    TRUE

---------------------

=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl

