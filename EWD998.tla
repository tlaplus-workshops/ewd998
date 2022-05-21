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

----- MODULE EWD998 ----
EXTENDS Integers

CONSTANT N

ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES 
  pending,              \* number of messages pending at a node (network)
  
  token,
  \* tokenLocation,        \* machine holding the token
  \* tokenValue,           \* sum of the pending messages seen so far
  \* tokenTainted,         \* has the token left a tainted node last?

  active,               \* activation status of nodes
  tainted,               \* tainted status of nodes
  counter               \* Each maintains counter of sent and received msgs.

  vars == << active, pending, tainted, token, counter >>

-----------------------------------------------------------------------------

terminationDetected ==
    \* Initiator has token
    /\ token.location = 0
    \* Initiator is done
    /\ active[0] = FALSE
    /\ tainted[0] = FALSE
    \* Nobody is tainted.
    /\ token.tainted = FALSE
    \* no more messages in flight
    /\ token.value + counter[0] = 0

terminated ==
    \A n \in Node: active[n] = FALSE /\ pending[n] = 0

TypeOK ==
    /\ pending \in [ Node -> Nat ]
    /\ active \in [ Node -> BOOLEAN ]
    /\ token \in [ location: Node, value: Int, tainted: BOOLEAN ]
    /\ counter \in [ Node -> Int ] \* [Node -> [sent: Nat, received: Nat ]]
    /\ tainted \in [Node-> BOOLEAN ]

Init ==
    /\ pending \in [ Node -> {0} ]
    /\ token = [location |-> N-1, value |-> 0, tainted |-> TRUE]
    /\ active \in [ Node -> BOOLEAN ]
    /\ tainted \in [Node-> {FALSE}]
    /\ counter \in [Node-> {0}]

InitiateToken ==
    \* TODO ??? inactive?
    \* /\ ~active[0]
    /\ ~terminationDetected
    /\ token.location = 0
    /\ token' = [location |-> N-1, value |-> 0, tainted |-> FALSE]
    /\ tainted' = [tainted EXCEPT ![token.location] = FALSE]
    /\ UNCHANGED <<active, counter, pending>>

PassToken ==
    /\ token.location # 0
    /\ ~active[token.location]
    /\ token' = [location |-> (token.location - 1), 
                 value |-> token.value + counter[token.location],
                 tainted |-> IF tainted[token.location] = TRUE THEN TRUE ELSE token.tainted ]
    \* /\ token.tainted' \in { token.tainted, ~active[token.location']}
    /\ tainted' = [tainted EXCEPT ![token.location] = FALSE]
    /\ UNCHANGED <<pending, active, counter>>

Terminates(n) ==
    /\ pending[n] = 0
    /\ active' = [ active EXCEPT ![n] = FALSE ]
    /\ pending' = pending
    /\ UNCHANGED << tainted, counter >>
    /\ UNCHANGED token

SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ pending' = [pending EXCEPT ![rcv] = @ + 1 ]
    /\ active' = active
    /\ counter' = [counter EXCEPT  ![snd] = @ + 1]
    /\ UNCHANGED tainted
    /\ UNCHANGED token

RecvMsg(rcv) ==
    /\ pending[rcv] > 0
    /\ pending' = [ pending EXCEPT ![rcv] = @ - 1 ]
    /\ active' = [active EXCEPT ![rcv] = TRUE ]
    \* TODO Can we move this to SendMsg?
    /\ tainted' = [tainted EXCEPT ![rcv] = TRUE]
    /\ counter' = [counter EXCEPT ![rcv] = @ - 1]
    /\ UNCHANGED token

Next ==
    \E n, m \in Node:
       \/ Terminates(n)
       \/ RecvMsg(n)
       \/ SendMsg(n, m)
       \/ PassToken
       \/ InitiateToken

Spec == 
    Init /\ [][Next]_vars /\ WF_vars(PassToken \/ InitiateToken)

ATD == INSTANCE AsyncTerminationDetection

ATDSpec == ATD!Spec

Implements ==
    Spec => ATD!Spec

\* Safe ==
\*     [](terminationDetected => terminated)

\* Live ==
\*     terminated ~> terminationDetected

=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl