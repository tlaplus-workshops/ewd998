---------------------- MODULE EWD998 ---------------------
\* * TLA+ is an expressive language and we usually define operators on-the-fly.
 \* * That said, the TLA+ reference guide "Specifying Systems" (download from:
 \* * https://lamport.azurewebsites.net/tla/book.html) defines a handful of
 \* * standard modules.  Additionally, a community-driven repository has been
 \* * collecting more modules (htteieeccnhcvitkvvennunlhkbunjfvdivdclbdcnvcdff
 \* * p://modules.tlapl.us). In our spec, we are
 \* * going to need operators for natural numbers.
EXTENDS Integers, TLC

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
Node == 0 .. N-1

Max2(S) == CHOOSE n \in S: \A m \in S: n>=m

Initiator ==
    CHOOSE n \in Node: TRUE

\* * Contrary to constants above, variables may change value in a behavior:
 \* * The value of active may be 23 in one state and "frob" in another.
 \* * For EWD998, active will maintain the activation status of our nodes,
 \* * while network counts the in-flight messages from other nodes that a
 \* * node has yet to receive.
VARIABLES
  active,               \* activation status of nodes
  network,
  inflight,
  token,
  msgSentNotTainted \* per-node boolean to track if a node has sent a message but not yet marked the token as tainted


\* * A definition that lets us refer to the spec's variables (more on it later).
vars == << active, network, inflight, token, msgSentNotTainted >>

\* z ==
\*     \A n \in Node: network[n] = 0 /\ ~active[n]

-----------------------------------------------------------------------------

\* Happens each time the token makes a full loop back to the initiator (Node 0)
\* Create a new, fresh token
InitiateToken(n) ==
    /\ n = Initiator
    /\ token.pos = n
    /\ active[n] = FALSE \* Is this needed?
    /\ token' = [ tainted |-> msgSentNotTainted[n] \/ token.value # 0, value |-> inflight[n], pos |-> N-1]
    /\ token' = [ token EXCEPT !["tainted"] = msgSentNotTainted[n] \/ token.value # 0 ,
                               !["value"] = inflight[n],
                               !["pos"] = N-1]
    /\ msgSentNotTainted' = [ msgSentNotTainted EXCEPT ![n] = FALSE ] \* reset the msg-sent status for the node passing the token
    /\ UNCHANGED << active, network, inflight >>

PassToken(n) ==
    /\ active[n] = FALSE
    /\ token.pos = n
    /\ token.pos # Initiator
    \* /\ token.value' = token.value + inflight[n]
    \* /\ token.pos' = (token.pos + 1) % N

    /\ token' = [ tainted |-> token.tainted \/ msgSentNotTainted[n], value |-> token.value + inflight[n], pos |-> (token.pos - 1)]
    \* /\ token.tainted' = (token.tainted \/ msgSentNotTainted[n]) \* taint the token if this node sent a msg
    /\ msgSentNotTainted' = [ msgSentNotTainted EXCEPT ![n] = FALSE ] \* reset the msg-sent status for the node passing the token
    /\ UNCHANGED << active, network, inflight  >>

-----------

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> {0} ]
    /\ inflight = [ n \in Node |-> 0 ]
    /\ token = [ tainted |-> TRUE, pos |-> 0, value |-> 0 ]
    /\ msgSentNotTainted = [ n \in Node |-> IF n=0 THEN TRUE ELSE FALSE ]

RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ active' = [ active EXCEPT ![rcv] = TRUE ]
    /\ network' = [ network EXCEPT ![rcv] = @ - 1 ]
    /\ inflight' = [ inflight EXCEPT ![rcv] = @ - 1 ]
    /\ UNCHANGED << token, msgSentNotTainted >>


SendMsg(snd, rcv) ==
    /\ network' = [ network EXCEPT ![rcv] = @ + 1]
    /\ active[snd] = TRUE
    \* /\ active' = [ active EXCEPT ![rcv] = FALSE ]
    /\ inflight' = [ inflight EXCEPT ![snd] = @ + 1 ]
    /\ msgSentNotTainted' = [ msgSentNotTainted EXCEPT ![snd] = TRUE ]
    /\ UNCHANGED active \* ??? Should a node deactivate after sending?
    /\ UNCHANGED << token >>

Terminate(n) ==
    \* /\ active[n] = TRUE
    /\ active' = [ active EXCEPT ![n] = FALSE ]
    /\ UNCHANGED << network, inflight, token, msgSentNotTainted >>

Next ==
    \E i,j \in Node:
        \/ SendMsg(i,j)
        \/ RecvMsg(i)
        \/ Terminate(i)
        \/ InitiateToken(i)
        \/ PassToken(i)

Invariant ==
    \A n \in Node: network[n] = 0

Property2 ==
    [Next]_vars

    \*  ( [A]_v )  <=>  (A \/ UNCHANGED v)
-------------------

terminationDetected ==
    /\ token.pos = 0
    /\ token.tainted = FALSE
    /\ token.value = 0
    /\ ~active[0]
    /\ ~msgSentNotTainted[0]

Spec ==
    /\ Init
    /\ [][Next]_vars
    \* /\ <>terminationDetected
    \* /\ WF_vars(Next)
    /\ \A i \in Node: WF_vars(PassToken(i) \/ InitiateToken(i))


\*   [A]_v   <=>   A \/ UNCHANGED v
\*  <<A>>_v  <=>   A /\ v # v'

\*  ENABLED <<A>>_v

\* <>[]P
\* []<>P

\* WF_v(A)  <=>   <>[] ENABLED <<A>>_v  =>  []<> <<A>>_v
\* SF_v(A)  <=>   []<> ENABLED <<A>>_v  =>  []<> <<A>>_v

\* ATD == INSTANCE AsyncTerminationDetection WITH pending <- network

\* ATDSpec == ATD!Spec

\* THEOREM Spec => ATD!Spec

\* refinement here messes up with the initial value of terminationDetected
\* so moved the checking to this file again

terminated ==
    \A n \in Node: network[n] = 0 /\ ~active[n]

Safe ==
    \* IF terminationDetected THEN terminated ELSE TRUE
    [](terminationDetected => terminated)
THEOREM Spec => Safe

Live ==
    \* [](terminated => <>terminationDetected)
    terminated ~> terminationDetected

THEOREM Spec => Live

TypeOK ==
    /\ network \in [ Node -> Nat]
    /\ active \in [ Node -> BOOLEAN ]
    /\ inflight \in [ Node -> Int]
    /\ msgSentNotTainted \in [ Node -> BOOLEAN ]
    \* /\ token \in [pos: Node, tainted: BOOLEAN, value: Int]
    \* /\ DOMAIN token = {"pos", "tainted", "value"}
    \* /\ token.pos \in Node
    \* /\ token.tainted \in BOOLEAN
    \* /\ token.value \in Int
    /\ token \in [ pos: Node, value: Int, tainted: BOOLEAN ]


THEOREM Spec => []TypeOK

---------------------------------

Fooo ==
    TLCGet("level") < 10

Constraint ==
    \A i \in Node: network[i] < 3 /\ inflight[i] \in (-2..2)


MCInit ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> {0} ]
    /\ inflight = [ n \in Node |-> 0 ]
    /\ token = [ tainted |-> TRUE, pos |-> 0, value |-> 0 ]
    /\ msgSentNotTainted = [ n \in Node |-> IF n=0 THEN TRUE ELSE FALSE ]
    \* we initiated the 0th node to be tainted to make sure the token at least go a round
    \* before terminationDetected is set to true
    \* simply setting tainted |-> TRUE in L214 is not enough as L71 will overwrite
--------

Sum2(fun, from, to) ==
    \*TODO
    LET sum[ i \in from..to ] ==
            IF i = from THEN fun[i]
            ELSE fun[i] + sum[i-1]
    IN IF from > to THEN 0 ELSE sum[to]

RECURSIVE Sum(_,_,_)
Sum(fun, from, to) ==
    IF from > to THEN 0
    ELSE fun[from] + Sum(fun, from+1, to)

B ==
    Sum(network, 0, N-1)

\* Fortunately, the EWD998 paper gives an inductive invariant in the form of a
 \* larger formula  P0 /\ (P1 \/ P2 \/ P3 \/ P4)  , with  \S  representing
 \* "the sum of",  B  to equal the sum of in-flight messages,  and  P0  to  P4 :
 \*
 \* P0: B = Si: 0 <= i < N: c.i)
 \* P1: (Ai: t < i < N: machine nr.i is passive) /\
 \*     (Si: t < i < N: c.i) = q
 \* P2: (Si: 0 <= i <= t: c.i) + q > 0
 \* P3: Ei: 0 <= i <= t : machine nr.i is black
 \* P4: The token is black

 \* We are implemnting a variant of EWD 840 so I assume EWD998's invariant doesn't really work?
IInv ==
    \* /\ P0:: B = Sum(inflight, 0, N-1)
    \* /\ \/ P1:: /\ \A i \in token.pos+1..N-1: active[i] = FALSE
    \*            /\ Sum(inflight, token.pos+1, N-1) = token.value
    \*    \/ P2:: Sum(inflight, 0, token.pos) + token.value > 0 \* P2
    \*    \/ P3:: \E i \in 0..token.pos: msgSentNotTainted[i] \* P3
    \*    \/ P4:: token.tainted = TRUE
    \/ P0:: \A i \in Node : token.pos < i => ~ active[i]
    \/ P1:: \E j \in 0 .. token.pos : msgSentNotTainted[j] = TRUE
    \/ P2:: token.tainted = TRUE


Alias == [
  active |-> active,               \* activation status of nodes
  network |-> network,
  inflight |-> inflight,
  token  |->  token,
  msgSentNotTainted |-> msgSentNotTainted,
  td |-> terminationDetected,
  p0  |-> IInv!P0,
  p1  |-> IInv!P1,
  p2  |-> IInv!P2
\*   p3  |-> IInv!P3,
\*   p4  |-> IInv!P4
]
=============================================================================
