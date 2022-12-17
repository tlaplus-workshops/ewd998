---------------------- MODULE AsyncTerminationDetection ---------------------
\* * TLA+ is an expressive language and we usually define operators on-the-fly.
 \* * That said, the TLA+ reference guide "Specifying Systems" (download from:
 \* * https://lamport.azurewebsites.net/tla/book.html) defines a handful of
 \* * standard modules.  Additionally, a community-driven repository has been
 \* * collecting more modules (http://modules.tlapl.us). In our spec, we are
 \* * going to need operators for natural numbers.
EXTENDS Naturals

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

VARIABLE (*bool[]*) active, network, terminationDetected
vars == << active, network, terminationDetected >>

terminated ==
    \A n \in Node: ~ active[n] /\ network[n] = 0

Init ==
    /\ network \in [ Node -> 0..3 ]
    \* /\ network = [ n \in Node |-> 0 ]
    /\ active \in [ Node -> BOOLEAN ]
    /\ \/ terminationDetected = FALSE
       \/ terminationDetected = terminated

SendMsg(snd, rcv) ==
    \* /\ snd # rcv
    \* /\ network[rcv]++
    /\ network' = [ n \in Node |-> IF n = rcv THEN network[n] + 1 ELSE network[n] ]
    /\ UNCHANGED active
    \* ??? Sender becomes active ???
    /\ active[snd] = TRUE
    /\ UNCHANGED terminationDetected

RecvMsg(rcv) ==
    /\ UNCHANGED terminationDetected
    /\ network[rcv] > 0
    /\ network' = [ n \in Node |-> IF n = rcv THEN network[n] - 1 ELSE network[n] ]
    /\ active' = [ n \in Node |-> IF n = rcv THEN TRUE ELSE active[n] ]

Idle(m) ==
    \* ??? Should we check network for empty? 
    \* /\ active' = [ n \in Node |-> IF n = m THEN FALSE ELSE active[n] ]
    /\ active' = [ active EXCEPT ![m] = FALSE ]
    /\ UNCHANGED network
    /\ \/ terminationDetected' = terminated'
       \/ terminationDetected' = terminationDetected
    \*    \/ terminationDetected' = TRUE
       
Next ==
    \E n,m \in Node:
        \/ Idle(n)
        \/ RecvMsg(n)
        \/ SendMsg(n,m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------

TypeOK ==
    /\ terminationDetected \in BOOLEAN 
    \* /\ \A n \in Node: active[n] \in BOOLEAN
    \* /\ Node = DOMAIN active
    /\ active \in [ Node -> BOOLEAN ]
    \* /\ \A n \in Node: network[n] \in Nat
    \* /\ Node = DOMAIN network
    /\ network \in [ Node -> Nat ]

Safe ==
    \* If we detect termination, there is termination.
    \* IF terminationDetected THEN terminated ELSE TRUE
    [](terminationDetected => terminated)

THEOREM Spec => Safe

Live  ==
    [](terminated => <>terminationDetected)

THEOREM Spec => Live

NeverTerminantes ==
    []~terminated

\* Implements == 
\*     /\ Spec => TypeOK
\*     /\ Spec => Safe
\*     /\ Spec => Live


---------------------

Constraint ==
    \A n \in Node: network[n] < 3

=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl

counter, tokenPosition, 
PassToken