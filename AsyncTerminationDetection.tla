---------------------- MODULE AsyncTerminationDetection ---------------------
\* * TLA+ is an expressive language and we usually define operators on-the-fly.
 \* * That said, the TLA+ reference guide "Specifying Systems" (download from:
 \* * https://lamport.azurewebsites.net/tla/book.html) defines a handful of
 \* * standard modules.  Additionally, a community-driven repository has been
 \* * collecting more modules (http://modules.tlapl.us). In our spec, we are
 \* * going to need operators for natural numbers.
EXTENDS Naturals, TLC

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
  pending               \* number of messages pending at a node
  , terminationDetected

\* * A definition that lets us refer to the spec's variables (more on it later).
vars == << active, pending, terminationDetected >>

-----------------------------------------------------------------------------

terminated ==
    \A n \in Node: active[n] = FALSE /\ pending[n] = 0

\* ??? Giffy: isnt this a language to express the algorithms and correctness of the program?
TypeOK ==
    /\ pending \in [ Node -> Nat ]
    /\ active \in [ Node -> BOOLEAN ]
    /\ terminationDetected \in BOOLEAN

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> Nat ]
    /\ terminationDetected \in {FALSE, terminated}

Terminates(n) ==
    /\ pending[n] = 0 \* TODO ???
    \* /\ active[n] = TRUE  \* TODO ???
    /\ active' = [ active EXCEPT ![n] = FALSE ]
    /\ pending' = pending
    /\ terminationDetected' \in {terminationDetected, terminated'}

SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ pending' = [pending EXCEPT ![rcv] = @ + 1 ]
    /\ active' = active
    /\ UNCHANGED terminationDetected

RecvMsg(rcv) ==
    /\ pending[rcv] > 0
    /\ pending' = [ pending EXCEPT ![rcv] = @ - 1 ]
    /\ active' = [active EXCEPT ![rcv] = TRUE ]
    /\ UNCHANGED terminationDetected

DetectTermination ==
    /\ terminated
    /\ terminationDetected' = TRUE
    /\ UNCHANGED <<active, pending>>

Next ==
    \E n, m \in Node:
       \/ Terminates(n)
       \/ RecvMsg(n)
       \/ SendMsg(n, m) \* TODO n#m ???
       \/ DetectTermination

Safe ==
    [](terminationDetected => []terminated)

---------------------

\* ENABLED A <=> Enablement condition of A evaluate to TRUE, state-level operator.
\* [A]_v     <=> A \/ UNCHANGED v
\* <<A>>_v   <=> A /\ v' # v
\* WF_v(A)   <=> <>[]ENABLED <<A>>_v => []<><<A>>_v
\* SF_v(A)   <=> []<>ENABLED <<A>>_v => []<><<A>>_v

Live ==
    \* [](terminated => <>[]terminationDetected)
    terminated ~> []terminationDetected

Spec == 
    /\ Init
    /\ [][Next]_vars
    \* /\ WF_vars(Next) \* works, because WF_vars isn't distributive.
    /\ WF_vars(DetectTermination)

THEOREM Spec => Live

THEOREM Spec => Safe

=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl