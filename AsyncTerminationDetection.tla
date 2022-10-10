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



Node == 0 .. N-1

VARIABLE active, network, terminationDetected

terminated ==
    \A n \in Node: network[n] = 0 /\ ~ active[n]

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> Nat ]
    /\ terminationDetected \in BOOLEAN 

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> 0..3 ]
    /\ terminationDetected \in {FALSE, terminated}

Idle(n) ==
    \* /\ network[n] = 0 \* a node uses global knowledge
    \* /\ active' = [ i \in Node |-> IF i = n THEN FALSE ELSE active[i] ]
    \* /\ \E m \in Node: active[m] = TRUE
    \* /\ active[n]
    /\ active' = [ active EXCEPT ![n] = FALSE ]
    /\ UNCHANGED network
    /\ \/ terminationDetected' = terminated'
       \/ UNCHANGED terminationDetected
    \*    \/ terminationDetected' = TRUE
    \* /\ terminationDetected' \in {terminationDetected, terminated'}

RecvMsg(rcv) ==
    /\ network' = [ network EXCEPT ![rcv] = @ - 1  ]
    /\ network[rcv] > 0
    /\ active' = [ i \in Node |-> IF i = rcv THEN TRUE ELSE active[i] ]
    /\ UNCHANGED terminationDetected
    \* /\ active' # active
    \* /\ network' = 42

SendMsg(snd, rcv) ==
    /\ network' = [ i \in Node |-> IF i = rcv THEN network[i] + 1 ELSE network[i] ]
    /\ active' = active
    /\ UNCHANGED active
    /\ active[snd]
    /\ UNCHANGED terminationDetected
   
Next ==
    \E i,j \in Node:
        \/ SendMsg(j,i)
        \/ RecvMsg(j)
        \/ Idle(i)

NeverUndetects ==
    terminationDetected => terminationDetected'

vars == <<active, network, terminationDetected>>

\* []<>Something   ("repeatedly")

\* <>[]Something   (" from somepoint forever ")

\* <>Something     (" once or more in the future")

Spec ==
    \* WHat is allowed to happen
    /\ Init
    /\ [][Next]_vars
    
    \* What must happen
    \* /\ <>[](ENABLED <<A>>_vars) => []<><<A>>_vars
    /\ WF_vars(\E n \in Node: Idle(n))

    \* /\ []<>(ENABLED <<A>>_vars) => []<><<\E n \in Node: Idle(n)>>_vars
    \* /\ SF_vars(\E n \in Node: Idle(n))

    \* /\ WF_vars(Next)
    \* /\ <>terminationDetected


    \* <<Next>>_vars  <=>      Next /\ vars' # vars
    \* [Next]_vars    <=>      Next \/ UNCHANGED vars

Safety ==
    [](terminationDetected => terminated)

THEOREM Spec => Safety

Live ==
    \* [](terminated => <>terminationDetected)
    terminated ~> []terminationDetected

THEOREM Spec => Live
---------

Alias ==
    [
        active |-> active, network |-> network
        , terminationDetected |-> terminationDetected,
        eIdle |-> \E n \in Node: ENABLED Idle(n)
    ]


Constraint ==
    \* Onlyl for model-checking!!!
    \A n \in Node: network[n] < 4

=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl