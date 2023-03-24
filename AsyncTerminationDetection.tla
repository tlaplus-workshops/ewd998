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
NIsPosNat == N \in Nat \ {0}

ASSUME NIsPosNat

Node == 0 .. N - 1 

VARIABLE active, network, terminationDetected
vars == <<active, network, terminationDetected>>

terminated ==
    \A n \in Node: active[n] = FALSE /\ network[n] = 0

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> Nat ]
    /\ terminationDetected \in BOOLEAN  

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> 0..3 ]
    /\ terminationDetected \in {FALSE, terminated}

Terminates(n) ==
    \* /\ active[n] = TRUE
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<network>>
    /\ terminationDetected' \in {terminationDetected}
    \* /\ \/terminationDetected' = terminated'
    \*    \/terminationDetected' = terminationDetected

SendMsg(snd, rcv) ==
    /\ UNCHANGED active
    /\ active[snd] = TRUE
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]
    /\ UNCHANGED terminationDetected

RecvMsg(rcv) ==
    /\ network[rcv] > 0
    /\ UNCHANGED terminationDetected
    \* /\ active[rcv] = TRUE \* ???
    /\ active' = [active EXCEPT ![rcv] = TRUE]
    /\ network' = [ network EXCEPT ![rcv] = network[rcv] - 1 ]

Next ==
    \E n,m \in Node:
        \/ Terminates(n)
        \/ SendMsg(n,m)
        \/ RecvMsg(n)

    \*   [A]_v     <=>      A \/ UNCHANGED v

Spec ==
    Init /\ [] [Next]_vars /\ WF_vars(Next)

-------------------

NeverUndetect ==
    [] [terminationDetected => terminationDetected']_vars

Safe ==
    [](terminationDetected => terminated)

Live ==
    [](terminated => <>terminationDetected)

THEOREM Spec => Safe    \*/\ NeverUndetect /\ Live

-------------------

Constraint ==
    \A n \in Node: network[n] < 3

=============================================================================
