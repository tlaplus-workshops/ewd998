---------------------- MODULE EWD998 ---------------------
EXTENDS Integers

Range(f) ==
    { f[x] : x \in DOMAIN f }

CONSTANT N

ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

Color == {"white", "black"}

VARIABLES 
  active,               \* activation status of nodes
  tainted,
  score,
  
  \* Network:
  pending,               \* number of messages pending at a node

  token_pos,
  token_tainted,
  token_score

\* * A definition that lets us refer to the spec's variables (more on it later).
vars == << active, pending, score, tainted, token_pos, token_score, token_tainted >>

terminated ==
    \A n \in Node: active[n] = FALSE /\ pending[n] = 0

terminationDetected ==
    /\ token_pos = 0
    /\ token_score + score[0] = 0
    /\ token_tainted = "white"
    /\ tainted[0] = "white"
    /\ active[0] = FALSE

-----------------------------------------------------------------------------

\* * Initially, all nodes are active and no messages are pending.
Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ score = [n \in Node |-> 0]
    /\ tainted = [n \in Node |-> "white"]

    /\ pending = [ n \in Node |-> 0 ]

    /\ token_pos \in Node
    /\ token_score = 0
    /\ token_tainted = "black"
    

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> Nat ]
    /\ token_pos \in Node
    /\ token_score \in Int
    /\ token_tainted \in Color
    /\ score \in [Node -> Int]
    /\ tainted \in [Node -> Color]
    
-----------------------------------------------------------------------------
TokenPass ==
    /\ token_pos # 0
    /\ active[token_pos] = FALSE
    /\ token_pos' = token_pos - 1
    /\ token_tainted' = IF tainted[token_pos] = "white" 
                        THEN token_tainted ELSE "black"
    /\ tainted' = [ tainted EXCEPT ![token_pos] = "white"]
    /\ token_score' = token_score + score[token_pos]
    /\ UNCHANGED <<score, active, pending>> 

InitiateToken ==
    /\ ~terminationDetected
    /\ active[0] = FALSE
    /\ token_pos = 0
    /\ token_pos' = N-1
    /\ token_tainted' = "white"
    /\ tainted' = [ tainted EXCEPT ![0] = "white"]
    /\ token_score' = 0
    /\ UNCHANGED <<score, active, pending>>

-------------------------------------------------------

Terminate(i) ==
    /\ active[i] = TRUE
    /\ active' = [ active EXCEPT ![i] = FALSE ]
    /\ pending' = pending
    /\ UNCHANGED <<tainted, score>>
    /\ UNCHANGED <<token_pos, token_score, token_tainted>>

\* * Node i sends a message to node j.
SendMsg(i, j) ==
    /\ i # j
    /\ active[i]
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ score' = [score EXCEPT ![i] = @ + 1]
    /\ UNCHANGED <<active, tainted, token_pos, token_tainted, token_score>>

\* * Node I receives a message.
Wakeup(i) ==
    /\ active[i] = FALSE
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ score' = [score EXCEPT ![i] = @ - 1]
    /\ tainted' = [tainted EXCEPT ![i] = "black"]
    /\ UNCHANGED <<token_pos, token_score, token_tainted>>

Next ==
    \/ InitiateToken
    \/ TokenPass
    \/ \E i,j \in Node:   
        \/ Terminate(i)
        \/ Wakeup(i)
        \/ SendMsg(i, j)

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)


-------------------------------------------

ATD == INSTANCE AsyncTerminationDetection

ATDSpec == ATD!Spec
THEOREM Implements == Spec => ATDSpec

=============================================================================
Safe ==
    terminationDetected => terminated

Live ==
    [](terminated => <>terminationDetected)

