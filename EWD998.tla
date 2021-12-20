------ MODULE EWD998 -----
EXTENDS Integers

CONSTANT N

ASSUME NIsPosNat == N \in Nat \ {0}

Color == {"white", "black"}

Node == 0 .. N-1

VARIABLES 
\* network
  pending,              \* number of messages pending at a node
\*nodes
  active,               \* activation status of nodes
  color,
  counter,  
\* token
  token

vars == << active, pending, color, counter, token >>

terminated ==
    \A n \in Node: /\ ~ active[n]
                   /\ pending[n] = 0

TypeOK ==
    /\ pending \in [ Node -> Nat ]
    /\ active \in [ Node -> BOOLEAN ]
    /\ counter \in [ Node -> Int ] 
    /\ color \in [ Node -> Color ]
    /\ token \in [ pos: Nat, color: Color, q: Int ]

-----------------------------------------------------------------------------

\* * Initially, all nodes are active and no messages are pending.
Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ color \in [ Node -> Color ] \* ????
    /\ pending \in [ Node -> {0} ]
    /\ counter \in [ Node -> {0} ]
    /\ token \in [ pos: {0}, q: {0}, color: Color ] \* ????

-----------------------------------------------------------------------------

InitatesToken ==
    /\ token.pos = 0
    /\ \/ token.color = "black" 
       \/ token.q + counter[0] # 0
    /\ token' = [ pos |-> N - 1,
                  q |-> 0,
                  color |-> "white" ] 
    /\ UNCHANGED <<active, pending, counter, color>>

PassToken(n) ==
    /\ ~active[n]
    /\ token.pos = n
    /\ token' = [ pos |-> token.pos - 1,
                  q |-> token.q + counter[n],
                  color |-> IF color[n] = "black" THEN "black" ELSE token.color ]  \* ????
    /\ UNCHANGED <<active, pending, counter, color>>

System ==
    \/ \E n \in Node \ {0}: PassToken(n)
    \/ InitatesToken

-----------------------------------------------------------------------------

\* * Node i terminates.
Terminate(i) ==
    \* /\ active[i] = TRUE
    /\ active' = [ active EXCEPT ![i] = FALSE ]
    /\ UNCHANGED pending

\* * Node i sends a message to node j.
SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ pending' = [ pending EXCEPT ![rcv] = @ + 1 ]
    /\ counter' = [ pending EXCEPT ![snd] = @ + 1 ]
    /\ UNCHANGED <<active>>

\* * Node I receives a message.
Wakeup(rcv) ==
    \* /\ active[rcv] = TRUE \* ????
    /\ pending[rcv] > 0
    /\ pending' = [ pending EXCEPT ![rcv] = @ - 1 ]
    /\ counter' = [ pending EXCEPT ![rcv] = @ - 1 ]
    /\ active' = [ active EXCEPT ![rcv] = TRUE ]
    /\ UNCHANGED <<>>

Environment ==
        \E n, m \in Node: 
        \* /\ n # m \* ????
        \* /\ 
           \/ Terminate(n)
           \/ SendMsg(n, m)
           \/ Wakeup(n)

Next ==
    \/ System
    \/ Environment

Spec ==
    Init /\ [][Next]_vars \*/\ WF_vars(DetectTermination)


=============================================================================

Stable ==
    \* Safety:
    [](terminationDetected => terminated)

THEOREM Spec => Stable

---------------------------------------------------

Live ==
    \* Liveness:
    \* [](terminated => <>terminationDetected)
    terminated ~> terminationDetected

THEOREM Spec => Live
