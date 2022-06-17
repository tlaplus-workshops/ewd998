---------------------- MODULE EWD998 ---------------------
EXTENDS Naturals, Integers

CONSTANT N

ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

Initator == 0

VARIABLES 
  color,
  active,               \* activation status of nodes
  counter,

  pending,

  tokenCounter,
  tokenPos,
  tokenColor

terminated ==
    /\ \A n \in DOMAIN active: ~active[n]
    /\ \A n \in DOMAIN pending: pending[n] = 0

terminationDetected ==
    /\ tokenCounter + counter[0] = 0
    /\ tokenColor = "white"
    \* /\ ~active[0]
    \* /\ color[0] = "white"

\* * A definition that lets us refer to the spec's variables (more on it later).
vars == << active, pending, color, counter, tokenCounter, tokenPos, tokenColor >>

Color == {"black", "white"}

TypeOK ==
    [](
    /\ active \in [ Node -> BOOLEAN ]
    /\ counter \in  [ Node -> Int ]
    /\ color \in [ Node -> Color ]
    /\ pending \in [ Node -> Nat ]
    /\ tokenColor \in Color
    /\ tokenCounter \in Int
    /\ tokenPos \in Node
    )

Init ==
    /\ active \in [ Node -> BOOLEAN  ]
    /\ color \in [ Node -> Color ]
    /\ counter = [ n \in Node |-> 0 ]
    /\ pending = [ n \in Node |-> 0 ]
    /\ tokenColor = "black" \* Why???
    /\ tokenPos \in Node
    /\ tokenCounter = 0

PassToken ==
    \* The current non-initiator node has the token.
    /\ tokenPos # 0
    /\ active[tokenPos] = FALSE 
    /\ tokenPos' = tokenPos - 1
    /\ tokenCounter' = tokenCounter + counter[tokenPos]
    /\ tokenColor' = IF color[tokenPos] = "black" THEN "black" ELSE tokenColor
    /\ color' = [color EXCEPT ![tokenPos] = "white"]
    /\ UNCHANGED <<active, pending, counter>>

InitiateToken ==
    \* The initiator has the token.
    /\ tokenPos = 0
    \* /\ ~terminationDetected
    /\ \/ tokenCounter + counter[0] # 0
       \/ tokenColor = "black"
       \/ active[0]
       \/ color[0] = "black"
    /\ tokenPos' = N-1
    /\ tokenColor' = "white"
    /\ UNCHANGED <<active, pending, counter, color, tokenCounter>>

Terminate(n) ==
    /\ pending[n] = 0 \* ???
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<pending, color, counter>>
    /\ UNCHANGED <<tokenColor, tokenCounter, tokenPos>>
    
SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ UNCHANGED active
    /\ pending' = [pending EXCEPT ![rcv] = @ + 1]
    /\ counter' = [counter EXCEPT ![snd] = @ + 1]
    /\ UNCHANGED <<color, tokenColor, tokenCounter, tokenPos>>

RecvMsg(rcv) ==
    /\ active[rcv] = FALSE \* ???
    /\ pending[rcv] > 0
    /\ active' = [ active EXCEPT ![rcv] = TRUE ]
    /\ color' = [color EXCEPT ![tokenPos] = "black"]
    /\ pending' = [pending EXCEPT ![rcv] = @ - 1]
    /\ counter' = [counter EXCEPT ![rcv] = @ - 1]
    /\ UNCHANGED <<tokenColor, tokenCounter, tokenPos>>

Next ==
    \E n,m \in Node: 
        \/ Terminate(n)
        \/ RecvMsg(n)
        \/ SendMsg(n,m)

----------------

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(PassToken \/ InitiateToken)

ATD == INSTANCE AsyncTerminationDetection

ATDSpec == ATD!Spec

THEOREM Spec => ATD!Spec

Constraint ==
    \A n \in Node: /\ pending[n] < 3
                   /\ counter[n] \in -2..2

=====