---------------------- MODULE EWD998 ---------------------
EXTENDS Naturals, TLC, Integers

CONSTANT N

ASSUME NIsPosNat == N \in Nat \ {0} 

Node == 0 .. N-1                           \* == pp'ed as ≜

VARIABLE 
    token,

    counter,
    color,
    active,

    pending
    
vars == <<active, pending, color, counter, token>>

terminated ==
    \A n \in Node: active[n] = FALSE /\ pending[n] = 0

TypeOK ==
    /\ counter \in [ Node -> Int ]
    /\ color \in [ Node -> {"B", "W"} ]
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> Nat ]
    /\ token \in [counter: Int, position: Node, color: {"B", "W"}]

Init ==
    /\ counter \in [ Node -> {0}]
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> {0}]
    /\ token = [counter |-> 0, position |-> 0, color |-> "B"]
    /\ color \in [Node -> {"W"}]

Terminate(n) ==
    /\ active' = [ active EXCEPT ![n] = FALSE ]
    /\ UNCHANGED << pending, color, token, counter>>

SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    /\ pending' = [ pending EXCEPT ![rcv] =  @ + 1 ]
    /\ UNCHANGED active
    /\ counter' = [ counter EXCEPT ![snd] =  @ + 1 ]
    /\ UNCHANGED color
    /\ UNCHANGED token
    
Wakeup(n) ==
    /\ pending[n] > 0
    /\ pending' = [ pending EXCEPT ![n] =  @ - 1 ]
    /\ active' = [ active EXCEPT ![n] = TRUE ]
    /\ counter' = [ counter EXCEPT ![n] =  @ - 1 ]
    /\ color' = [ color EXCEPT ![n] = "B" ]
    /\ UNCHANGED token

PassToken ==
    LET snd == token.position IN
        /\ snd # 0
        /\ active[snd] = FALSE
        /\ token' = [ counter |-> token.counter + counter[snd],
                      color |-> IF color[snd] = "B" THEN color[snd] ELSE token.color,
                      position |-> token.position - 1
                    ]
        /\ color' = [ color EXCEPT ![snd] = "W" ]
        /\ UNCHANGED <<counter, pending, active>>

InitiateToken ==
    /\ token.position = 0
    /\ \/ token.color = "B"
       \/ token.counter + counter[0] > 0
       \/ active[0]
    /\ token' = [ counter |-> 0, color |-> "W", position |-> N - 1 ]
    /\ UNCHANGED <<counter, pending, active, color>>

Next ==
    \/ PassToken
    \/ InitiateToken
    \/ \E n,m \in Node:
        \/ Terminate(n)
        \/ SendMsg(n,m)
        \/ Wakeup(n)

Spec ==
    Init /\ [][Next]_vars

terminationDetected ==
    /\ active[0] = FALSE
    /\ color[0] = "W"
    /\ token.color = "W"
    /\ token.counter + counter[0] = 0
    /\ token.position = 0

ATD == INSTANCE AsyncTerminationDetection

ATDSpec == ATD!Spec

THEOREM Spec => ATDSpec

=============================================================================
