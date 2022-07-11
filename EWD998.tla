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
  pending,
  processed,
  tokenPosition,
  tokenValue,
  tokenTainted,
  msgSentNotTainted \* per-node boolean to track if a node has sent a message but not yet marked the token as tainted
  

\* * A definition that lets us refer to the spec's variables (more on it later).
vars == << active, pending, processed, tokenPosition, tokenValue, tokenTainted, msgSentNotTainted >>

terminated ==
    \A n \in Node: pending[n] = 0 /\ ~active[n]

-----------------------------------------------------------------------------

\* Happens each time the token makes a full loop back to the initiator (Node 0)
\* Create a new, fresh token
InitiateToken(n) ==
    /\ n = 0
    /\ tokenPosition = n
    /\ active[n] = FALSE \* Is this needed?
    /\ tokenTainted' = (msgSentNotTainted[n] \/ tokenValue # 0) \* taint the token if this node sent a msg    
    /\ tokenValue' = processed[n]
    \* /\ processed' = [ processed EXCEPT ![n] = 0 ] \* why does `processed` change here when passing a token?
    /\ msgSentNotTainted' = [ msgSentNotTainted EXCEPT ![n] = FALSE ] \* reset the msg-sent status for the node passing the token
    /\ tokenPosition' = (tokenPosition + 1) % N
    /\ UNCHANGED << active, pending, processed >>

PassToken(n) ==
    /\ active[n] = FALSE
    /\ tokenPosition = n
    /\ tokenPosition # 0
    /\ tokenValue' = tokenValue + processed[n]
    \* /\ processed' = [ processed EXCEPT ![n] = 0 ] \* why does `processed` change here when passing a token?
    /\ tokenPosition' = (tokenPosition + 1) % N
    /\ tokenTainted' = (tokenTainted \/ msgSentNotTainted[n]) \* taint the token if this node sent a msg
    /\ msgSentNotTainted' = [ msgSentNotTainted EXCEPT ![n] = FALSE ] \* reset the msg-sent status for the node passing the token
    /\ UNCHANGED << active, pending, processed  >>
-----------

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> {0} ] 
    /\ processed = [ n \in Node |-> 0 ] 
    /\ tokenPosition = 0
    /\ tokenTainted = TRUE
    /\ tokenValue = 0
    /\ msgSentNotTainted = [ n \in Node |-> FALSE ]

RecvMsg(rcv) ==
    /\ pending[rcv] > 0
    /\ active' = [ active EXCEPT ![rcv] = TRUE ] 
    /\ pending' = [ pending EXCEPT ![rcv] = @ - 1 ]
    /\ processed' = [ processed EXCEPT ![rcv] = @ + 1 ]
    /\ UNCHANGED << tokenPosition, tokenValue, tokenTainted, msgSentNotTainted >>


SendMsg(snd, rcv) ==
    /\ pending' = [ pending EXCEPT ![rcv] = @ + 1]
    /\ active[snd] = TRUE
    \* /\ active' = [ active EXCEPT ![rcv] = FALSE ] 
    /\ processed' = [ processed EXCEPT ![snd] = @ - 1 ]
    /\ msgSentNotTainted' = [ msgSentNotTainted EXCEPT ![snd] = TRUE ]
    /\ UNCHANGED active \* ??? Should a node deactivate after sending?
    /\ UNCHANGED << tokenPosition, tokenValue, tokenTainted >>


Terminate(n) ==
    \* /\ active[n] = TRUE 
    /\ active' = [ active EXCEPT ![n] = FALSE ]
    /\ UNCHANGED << pending, processed, tokenPosition, tokenValue, tokenTainted, msgSentNotTainted >>

Next ==
    \E i,j \in Node:
        \/ SendMsg(i,j)
        \/ RecvMsg(i)
        \/ Terminate(i)
        \/ InitiateToken(i)
        \/ PassToken(i)

-------------------

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* vars == << active, pending, processed, tokenPosition, tokenValue, tokenTainted, msgSentNotTainted >>

TypeOK ==
    /\ pending \in [ Node -> Nat]
    /\ active \in [ Node -> BOOLEAN ]
    /\ processed \in [ Node -> Int]
    /\ msgSentNotTainted \in [ Node -> BOOLEAN ]
    /\ tokenPosition \in Node
    /\ tokenValue \in Int 
    /\ tokenTainted \in BOOLEAN

---------------------

terminationDetected ==
    /\ tokenPosition = 0
    /\ tokenTainted = FALSE
    /\ tokenValue = 0
    /\ ~active[0]
    /\ ~msgSentNotTainted[0]
    \* /\ pending[0] = 0

Safe ==
    \* IF terminationDetected THEN terminated ELSE TRUE
    [](terminationDetected => terminated)

Live ==
    [](terminated => <>terminationDetected)


Constraint ==
    \A i \in Node: pending[i] < 3 /\ processed[i] \in (-2..2)


MCInit ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> {0} ] 
    /\ processed = [ n \in Node |-> 0 ] 
    /\ tokenPosition = 0
    /\ tokenTainted = TRUE
    /\ tokenValue = 0
    /\ msgSentNotTainted = [ n \in Node |-> FALSE ]

=============================================================================
