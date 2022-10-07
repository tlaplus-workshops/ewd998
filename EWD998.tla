---------------------- MODULE EWD998 ---------------------
\* * TLA+ is an expressive language and we usually define operators on-the-fly.
 \* * That said, the TLA+ reference guide "Specifying Systems" (download from:
 \* * https://lamport.azurewebsites.net/tla/book.html) defines a handful of
 \* * standard modules.  Additionally, a community-driven repository has been
 \* * collecting more modules (http://modules.tlapl.us). In our spec, we are
 \* * going to need operators for natural numbers.
EXTENDS Integers

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

VARIABLE
         active,
         color,
         counter,

         network,
         
         tokenPos,
         tokenQ,
         tokenColor


terminated ==
    \A n \in Node: network[n] = 0 /\ ~ active[n]

terminationDetected ==
    /\ tokenColor = "w"
    /\ tokenPos = 0
    \* /\ counter[0] = 0
    /\ tokenQ + counter[0] = 0
    \* \* 
    \* /\ \A n \in Node: network[n] = 0

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ counter \in [Node -> Int]
    /\ color \in [ Node -> {"w","b"} ]
    /\ network \in [ Node -> Nat ]
    /\ tokenPos \in Node
    /\ tokenColor \in {"w","b"}
    /\ tokenQ \in Int

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ counter \in [Node -> {0}]
    /\ color \in [ Node -> {"w","b"} ]
 
    /\ network \in [ Node -> {0} ]
 
    /\ tokenPos \in Node
    /\ tokenColor \in {"w","b"}
    /\ tokenQ \in {0}

PassToken(n) ==
    /\ tokenPos # 0
    /\ tokenPos = n
    /\ ~active[n]
    /\ tokenPos' = tokenPos - 1
    /\ tokenColor' = IF color[n] = "b" THEN "b" ELSE tokenColor
    /\ tokenQ' = counter[n] + tokenQ
    /\ color' =  [ color EXCEPT ![n] = "w" ]
    /\ UNCHANGED <<network, counter, active>>

InitiateToken ==
    /\ ~active[0] \* ???
    /\ tokenPos = 0
    /\ tokenPos' = N-1
    /\ tokenQ' = 0
    /\ tokenColor' = color[0]
    /\ color' = [ color EXCEPT ![0] = "w" ]
    /\ UNCHANGED <<network, counter, active>>

Idle(n) ==
    \* /\ network[n] = 0 \* a node uses global knowledge
    \* /\ active' = [ i \in Node |-> IF i = n THEN FALSE ELSE active[i] ]
    /\ active' = [ active EXCEPT ![n] = FALSE ]
    /\ UNCHANGED <<tokenColor, tokenQ, tokenPos, network, color, counter>>

RecvMsg(rcv) ==
    /\ network' = [ network EXCEPT ![rcv] = @ - 1  ]
    /\ network[rcv] > 0
    /\ active' = [ i \in Node |-> IF i = rcv THEN TRUE ELSE active[i] ]
    /\ color' = [ color EXCEPT ![rcv] = "b"]
    /\ counter' = [ counter EXCEPT ![rcv] = @ - 1]
    /\ UNCHANGED <<tokenColor, tokenQ, tokenPos>>

SendMsg(snd, rcv) ==
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]
    /\ counter' = [ counter EXCEPT ![snd] = @ + 1]
    /\ active' = active
    /\ UNCHANGED <<tokenColor, tokenQ, tokenPos, active, color>>
    /\ active[snd]
   
Next ==
    \E i,j \in Node:
        \/ SendMsg(j,i)
        \/ RecvMsg(j)
        \/ Idle(i)
        \/ PassToken(i)
        \/ InitiateToken

vars == <<active, network, tokenColor, tokenQ, tokenPos, color, counter>>
Spec ==
    Init /\ [][Next]_vars

\* EWD998 implemented ATD
ATD == INSTANCE AsyncTerminationDetection
Implements ==
    Spec => ATD!Spec

ATDSpec == ATD!Spec
---------

Constraint ==
    \* Onlyl for model-checking!!!
    \A n \in Node: network[n] < 3 /\ counter[n] \in -2..2 /\ tokenQ \in -2..2

=============================================================================
Safety ==
    [](terminationDetected => terminated)

