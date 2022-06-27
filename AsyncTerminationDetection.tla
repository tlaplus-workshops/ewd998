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
Node == 0 .. N-1


\* * Contrary to constants above, variables may change value in a behavior:
 \* * The value of active may be 23 in one state and "frob" in another.
 \* * For EWD998, active will maintain the activation status of our nodes,
 \* * while pending counts the in-flight messages from other nodes that a
 \* * node has yet to receive.
VARIABLES 
  active,               \* activation status of nodes
  pending,               \* number of messages pending at a node
  terminationDetected

\* * A definition that lets us refer to the spec's variables (more on it later).
vars == << active, pending, terminationDetected >>

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> Nat ]
    /\ terminationDetected \in BOOLEAN 

\* * Initially, all nodes are active and no messages are pending.
Init ==
    /\ active = [n \in Node |-> TRUE ] 
    /\ pending = [ n \in Node |-> 0] 
    /\ terminationDetected = FALSE

-----------------------------------------------------------------------------

terminated == 
    \A n \in Node: pending[n] = 0 /\ ~active[n]

\* * Each one of the definitions below represent atomic transitions, i.e., define
 \* * the next state of the current behavior (a state is an assignment of
 \* * values to variables). We call those definitions "actions". A next state is
 \* * possible if the action is true for some combination of current and next
 \* * values. Two or more actions do *not* happen simultaneously; if we want to
 \* * e.g. model things to happen at two nodes at once, we are free to choose an
 \* * appropriate level of granularity for those actions.

\* * Node i terminates.
Terminate(i)  ==
    \* /\ active[i] = TRUE \* ???
    /\ active' = [ n \in Node |-> IF i = n THEN FALSE ELSE active[n] ]
    \* /\ \/ terminationDetected' = terminated'
    \*    \/ UNCHANGED terminationDetected
    /\ UNCHANGED pending
    /\ terminationDetected' \in {terminationDetected, terminated'}

\* * Node i sends a message to node j.
SendMsg(i, j) ==
    /\ active[i]= TRUE \* ???? Could it be FALSE?
    /\ pending' = [ pending EXCEPT ![j] = @ + 1 ]
    /\ UNCHANGED active
    /\ UNCHANGED terminationDetected
    /\ UNCHANGED <<active, terminationDetected>>
    
\* * Node i receives a message.
Wakeup(i) ==
    \* /\ active[i] = FALSE \* ???
    /\ pending[i] > 0
    /\ pending' = [ pending EXCEPT ![i] = @ - 1 ]
    /\ active' = [ active EXCEPT ![i] = TRUE ]
    /\ UNCHANGED terminationDetected

DetectTermination ==
    /\ terminated
    /\ terminationDetected' = TRUE
    /\ UNCHANGED <<active, pending>>

Next ==
    \E n,m \in Node:
         \/ Terminate(n)
         \/ Wakeup(n)
         \/ SendMsg(n,m)
         \/ DetectTermination
    
Constraint ==
    \A n \in Node: pending[n] < 4

Spec == 
    Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

Safe ==
    \* IF terminationDetected THEN terminated ELSE TRUE
    [](terminationDetected => terminated)

THEOREM Spec => Safe

Live ==
    [](terminated => <>(terminationDetected))

THEOREM Spec => Live
=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl