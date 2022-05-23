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

(*

- Recursion
- Dijkstra's invariant

*)

terminationDetected ==
    \* Initiator has to have the token
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
    /\ token = [location |-> 0, value |-> 0, tainted |-> TRUE]
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

Environment ==
    \E n, m \in Node:
       \/ Terminates(n)
       \/ RecvMsg(n)
       \/ SendMsg(n, m)

System ==
    \/ PassToken
    \/ InitiateToken

Next == 
    System \/ Environment

Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(System)

ATD == INSTANCE AsyncTerminationDetection

ATDSpec == ATD!Spec

THEOREM Spec => ATDSpec

Implements ==
    Spec => ATD!Spec

\* Fortunately, the EWD998 paper gives an inductive invariant in the form of a
 \* larger formula  P0 /\ (P1 \/ P2 \/ P3 \/ P4)  , with  \S  representing
 \* "the sum of",  B  to equal the sum of in-flight messages,  and  P0  to  P4 : 
 \*
 \* P0: B = Si: 0 <= i < N: counter[i])
 \* P1: (Ai: token.location < i < N: color[i] is passive) /\
 \*     (Si: token.location < i < N: counter[i]) = token.value
 \* P2: (Si: 0 <= i <= token.location: counter[i]) + token.value > 0
 \* P3: Ei: 0 <= i <= token.location : color[i] is black
 \* P4: The token is black

RECURSIVE SumOf(_,_,_)
SumOf(f, from, to) ==
    IF from > to THEN 0 ELSE
    IF from = to
    THEN 0
    ELSE f[from] + SumOf(f, from + 1, to)

SumOfFunc(f, from, to) ==
    LET sum[ i \in from..to ] == 
        IF i = from THEN f[from] ELSE f[i] + sum[i-1]
    IN sum[to]

B == 
    SumOf(pending, 0, N-1)

indInv == 
    /\ P0:: B = SumOf(counter, 0, N-1)
    /\ \/ P1:: /\ \A i \in (token.location+1)..N-1 : tainted[i] = FALSE 
               /\ SumOf(counter, token.location + 1, N-1) = token.value
       \/ P2:: SumOf(counter, 0, token.location) + token.value > 0
       \/ P3:: \E i \in 0..token.location : tainted[i] = TRUE
       \/ P4:: token.tainted = TRUE
    
expr ==
    [
  pending |-> pending,
  token |-> token,
  active |->active,               \* activation status of nodes
  tainted |->tainted,               \* tainted status of nodes
  counter    |->counter,
  td |-> terminationDetected,
  ENext  |-> ENABLED Next,
  EPT  |-> ENABLED PassToken
     ]
 
=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl