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

Nodes ==
    0 .. N-1

VARIABLE messages, active, terminationDetected

termination ==
    \A n \in Nodes: active[n] = FALSE /\ messages[n] = 0

Init ==
    /\ active = [ n \in Nodes |-> TRUE ]
    /\ messages = [ n \in Nodes |-> 0]
    \* /\ terminationDetected \in {FALSE, termination}
    /\ \/ terminationDetected = FALSE
       \/ terminationDetected = termination

Idle(node) ==
    /\ active' = [ n \in Nodes |-> IF n = node THEN FALSE ELSE active[n]]
    /\ active' = [ active EXCEPT ![node] = FALSE' ]
    /\ messages' = messages
    /\ \/ terminationDetected' = termination'
       \/ terminationDetected' = terminationDetected

SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ messages' = [ n \in Nodes |-> IF n = rcv THEN messages[n] + 1 ELSE messages[n] ]
    /\ messages' = [ messages EXCEPT ![rcv] = messages[rcv] + 1 ]
    /\ messages' = [ messages EXCEPT ![rcv] = @ + 1 ]
    /\ active' = active
    /\ terminationDetected' = terminationDetected

RecvMsg(rcv) ==
    /\ messages[rcv] > 0
    /\ messages' = [ n \in Nodes |-> IF n = rcv THEN messages[n] - 1 ELSE messages[n] ]
    /\ active' = [ n \in Nodes |-> IF n = rcv THEN TRUE ELSE active[n]] 
    /\ terminationDetected' = terminationDetected

Next ==
    \E n, m \in Nodes: 
        \/ Idle(n)
        \/ SendMsg(n,m)
        \/ RecvMsg(n)

----

Inv ==
    \* IF terminationDetected THEN termination ELSE TRUE
    terminationDetected => termination
    \* terminationDetected = termination

Gooood ==
    termination => <>terminationDetected

OnlyThreeMsgs ==
    \A n \in Nodes: messages[n] < 4

=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl