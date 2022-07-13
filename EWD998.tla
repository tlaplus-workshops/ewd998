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

\* Hard-coded to 0. This can't be changed; other parts will break.
N0 == 0

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
  nodeTainted \* per-node boolean to track if a node has become tainted
  

\* * A definition that lets us refer to the spec's variables (more on it later).
vars == << active, network, inflight, token, nodeTainted >>

-----------------------------------------------------------------------------

terminationDetected ==
    /\ token.pos = N0
    /\ token.tainted = FALSE
    /\ token.value + inflight[N0] = 0
    /\ ~active[N0]
    /\ ~nodeTainted[N0]

\* Happens each time the token makes a full loop back to the N0 (Node 0)
\* Create a new, fresh token
InitiateToken(n) ==
    /\ n = N0
    /\ token.pos = N0
    /\ ~active[N0]
    /\ ~terminationDetected
   \* Rule 1
    /\ token' = [ token EXCEPT !["tainted"] = FALSE, \* Rule 6
                               !["value"] = 0,
                               !["pos"] = N - 1]  
    /\ nodeTainted' = [ nodeTainted EXCEPT ![N0] = FALSE ] \* Rule 6
    /\ UNCHANGED << active, network, inflight >>

PassToken(n) ==
    /\ ~active[n]
    /\ token.pos = n
    /\ token.pos # N0    
                               \* Rule 4
    /\ token' = [ token EXCEPT !["tainted"] = token.tainted \/ nodeTainted[n],
                               \* Rule 2
                               !["value"] = @ + inflight[n],
                               !["pos"] = @ - 1] 
   \* Rule 7                           
    /\ nodeTainted' = [ nodeTainted EXCEPT ![n] = FALSE ]
    /\ UNCHANGED << active, network, inflight  >>

-----------

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> {0} ] 
    /\ inflight = [ n \in Node |-> 0 ] 
    \* Initialize the token into a state as if it had just been initiated by n0
    /\ token = [ tainted |-> FALSE, pos |-> N - 1, value |-> 0 ]
    /\ nodeTainted = [ n \in Node |-> FALSE ]

RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ active' = [ active EXCEPT ![rcv] = TRUE ] 
    /\ network' = [ network EXCEPT ![rcv] = @ - 1 ]
    /\ inflight' = [ inflight EXCEPT ![rcv] = @ - 1 ]
    \* Rule 3
    /\ nodeTainted' = [ nodeTainted EXCEPT ![rcv] = TRUE ]
    /\ UNCHANGED << token >>


SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ network' = [ network EXCEPT ![rcv] = @ + 1]
    /\ inflight' = [ inflight EXCEPT ![snd] = @ + 1 ]
    /\ UNCHANGED << active, token, nodeTainted >>

Terminate(n) ==
    /\ active' = [ active EXCEPT ![n] = FALSE ]
    /\ UNCHANGED << network, inflight, token, nodeTainted >>

Next ==
    \E i,j \in Node:
        \/ SendMsg(i,j)
        \/ RecvMsg(i)
        \/ Terminate(i)
        \/ InitiateToken(i)
        \/ PassToken(i)


-------------------

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ (\A i \in Node: WF_vars(PassToken(i) \/ InitiateToken(i) \/ Terminate(i))) 


ATD == INSTANCE AsyncTerminationDetection WITH pending <- network 

ATDSpec == ATD!Spec

THEOREM Spec => ATD!Spec


TypeOK ==
    /\ network \in [ Node -> Nat]
    /\ active \in [ Node -> BOOLEAN ]
    /\ inflight \in [ Node -> Int]
    /\ nodeTainted \in [ Node -> BOOLEAN ]
    /\ token \in [ pos: Node, value: Int, tainted: BOOLEAN ]


THEOREM Spec => []TypeOK

---------------------------------

\* Bound pending messages to constrain the state
Constraint ==
    \A i \in Node: network[i] < 3 /\ inflight[i] \in (-2..2)


MCInit ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> {0} ] 
    /\ inflight = [ n \in Node |-> 0 ] 
    \* Initialize the token into a state as if it had just been initiated by n0
    /\ token = [ tainted |-> FALSE, pos |-> N - 1, value |-> 0 ]
    /\ nodeTainted = [ n \in Node |-> FALSE ]

--------

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

IInv ==
    /\ P0:: B = Sum(inflight, 0, N-1)
    /\ \/ P1:: /\ \A i \in token.pos+1..N-1: active[i] = FALSE
               /\ Sum(inflight, token.pos+1, N-1) = token.value
       \/ P2:: Sum(inflight, 0, token.pos) + token.value > 0
       \/ P3:: \E i \in 0..token.pos: nodeTainted[i]
       \/ P4:: token.tainted = TRUE


Alias == [
  active |-> active,               \* activation status of nodes
  network |-> network,
  inflight |-> inflight,
  token  |->  token,
  nodeTainted |-> nodeTainted,
  p0  |-> IInv!P0,
  p1  |-> IInv!P1,
  p2  |-> IInv!P2,
  p3  |-> IInv!P3,
  p4  |-> IInv!P4,
  term |-> terminationDetected
]
=============================================================================
