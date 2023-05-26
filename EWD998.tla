---- MODULE EWD998 ----
EXTENDS Integers, Sequences, Functions

CONSTANT N

ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1


VARIABLES
  active,               \* activation status of nodes
  counter,

  pending,               \* number of messages pending at a node

  token,
  color 

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ counter \in [Node -> Int]
    /\ pending \in [ Node -> Nat ]
    /\ token \in [ pos: Node, val: Int, color : {"white","black"} ] 
    /\ color \in [Node -> {"black","white"} ]

vars == << active, pending, counter, token, color >>

-----------------------------------------------------------------------------

terminated ==
    \A n \in Node: active[n] = FALSE /\ pending[n] = 0

terminationDetected ==
    /\ token.pos = 0
    /\ token.val = 0
    /\ token.color = "white"
    /\ active[0] = FALSE
    /\ color[0] = "white"

\* RECURSIVE SumO(_,_,_)
\* SumO(fun, from, to) ==
\*     IF from = to 
\*     THEN fun[to]
\*     ELSE fun[from] + SumO(fun, from+1, to)

\* Sum(fun, from, to) ==
\*     LET sum[ i \in from..to ] ==
\*             IF i = from
\*             THEN fun[i]
\*             ELSE sum[i-1] + fun[i]
\*     IN sum[to]

Sum(fun, from, to) ==
    FoldFunctionOnSet(+, 0, fun, from..to)

Pending2Counter ==
    Sum(pending, 0, N-1) = Sum(counter, 0, N-1)

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ counter \in [ Node -> -2..2 ]
    \* make the token black so the terminationDetected is not 
    \* TRUE at the Init
    /\ token \in [ pos: {0}, val: {0}, color: {"black"} ] 
    /\ pending \in [ Node -> 0..2 ]
    /\ Pending2Counter
    /\ color \in [Node -> {"white"}]

-----------------------------------------------------------------------------

InitiateToken ==
    /\ ~terminationDetected
    /\ token.pos = 0
    /\ token' = [ 
        pos |-> N - 1, 
        val |-> counter[0], 
        color |-> color[0] 
      ]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED << active, counter, pending >>

PassToken ==
    /\ active[token.pos] = FALSE
    /\ token.pos # 0
    /\ color' = [color EXCEPT ![token.pos] = "white"]
    /\ token' = [ 
        pos |-> token.pos - 1, 
        val |-> token.val + counter[token.pos], 
        color |-> IF color[token.pos] = "black" THEN "black" ELSE token.color 
      ]
    /\ UNCHANGED << active, counter, pending >>

\* * Node i terminates.
Terminate(i) ==
    /\ active' = [ active EXCEPT ![i] = FALSE ]
    /\ UNCHANGED << token, counter, pending, color >>

\* * Node i sends a message to node j.
SendMsg(i, j) ==
    \* /\ i # j \* ???
    /\ active[i] = TRUE
    /\ color' = [color EXCEPT ![i] = "black"]
    /\ counter' = [ counter EXCEPT ![i] = @ + 1 ]
    /\ pending' = [ pending EXCEPT ![j] = @ + 1 ]
    /\ UNCHANGED << active, token >>

\* * Node I receives a message.
Wakeup(i) ==
    /\ active[i] = FALSE \* ????
    /\ pending[i] > 0
    /\ color' = [color EXCEPT  ![i] = "black"]
    /\ counter' = [ counter EXCEPT ![i] = @ - 1 ]
    /\ active' = [ active EXCEPT ![i] = TRUE ]
    /\ pending' = [ pending EXCEPT ![i] = @ - 1 ]
    /\ UNCHANGED << token >>

Next ==
    \/ InitiateToken
    \/ PassToken
    \/ \E i, j \in Node: 
        \/ SendMsg(i,j)
        \/ Wakeup(i)
        \/ Terminate(i)

Spec ==
    /\ Init
    /\ [][Next]_vars 
    /\ WF_vars(InitiateToken \/ PassToken)
    /\ \A i \in Node: WF_vars(Terminate(i))

ATD == INSTANCE AsyncTerminationDetection

ATDSpec == ATD!Spec
--------

\* Ignore this if you don't care about TLC!
Constraint ==
    \A n \in Node: counter[n] \in -3..3

---------

Alias ==
    [
        active |-> active,
        counter |-> counter,
        pending |-> pending,
        token |-> token,
        td |-> terminationDetected,
        t |-> terminated,
        color |-> color
    ]
======