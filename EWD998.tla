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
  counter,
  color,

  pending,               \* number of messages pending at a node

  token

\* * A definition that lets us refer to the spec's variables (more on it later).
vars == << active, pending,counter, color,token >>

Color == {"black", "white"}

Initiator == CHOOSE n \in Node: TRUE

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> Nat ]
    /\ color \in [ Node -> Color ] 
    \* /\ token.color \in Color
    \* /\ token.pos \in Node
    \* /\ token.counter \in Int
    \* /\ DOMAIN token = {"pos", "color", "counter"}
    /\ token \in [ pos: Node, color: Color, counter: Int ] 
    /\ counter \in [ Node -> Int ]

\* * Initially, all nodes are active and no messages are pending.
Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ color \in [ Node -> Color ] 
    /\ counter = [ n \in Node |-> 0 ]

    /\ pending = [ n \in Node |-> 0] 

    \* /\ token = [ pos |-> 0, color |-> "black", counter|-> 0 ]
    /\ token \in [ pos: Node, color: {"black"}, counter: -3..3 ] 

-----------------------------------------------------------------------------

terminationDetected ==
    /\ color[0] = "white"
    /\ active[0] = FALSE
    /\ token.color = "white"
    /\ token.pos = 0
    /\ token.counter + counter[0] = 0
    \* /\ pending[0] = 0
    \* /\ tokenCounter = 0 \* ????
    \* /\ counter[0] = 0
    \* /\ FALSE

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
    /\ active' = [ n \in Node |-> IF i = n THEN FALSE ELSE active[n] ]
    /\ UNCHANGED pending
    /\ UNCHANGED <<token>>
    /\ UNCHANGED <<counter, color>>

\* * Node i sends a message to node j.
SendMsg(i, j) ==
    /\ active[i]= TRUE
    /\ pending' = [ pending EXCEPT ![j] = @ + 1 ]
    /\ counter' = [ counter EXCEPT ![i] = @ + 1 ]
    /\ UNCHANGED <<active, color>>
    /\ UNCHANGED <<token>>
    
\* * Node i receives a message.
Wakeup(i) ==
    \* /\ active[i] = FALSE \* ???/
    /\ pending[i] > 0
    /\ pending' = [ pending EXCEPT ![i] = @ - 1 ]
    /\ counter' = [ counter EXCEPT ![i] = @ - 1 ]
    /\ active' = [ active EXCEPT ![i] = TRUE ]
    /\ color'  = [ color EXCEPT ![i] = "black" ] \* should we change this?
    /\ UNCHANGED <<token>>

PassToken ==
    /\ token.pos # 0
    /\ active[token.pos] =  FALSE
    /\ token' = [ pos |-> token.pos - 1,
                  counter |-> token.counter + counter[token.pos],
                  color |-> IF color[token.pos] = "black" THEN "black" ELSE token.color ]
    /\ color'  = [ color EXCEPT ![token.pos] = "white" ] \* should we change this?
    /\ UNCHANGED <<active, pending, counter>>

InitiateToken ==
    /\ ~terminationDetected
    /\ token.pos = 0
    /\ token' = [ token EXCEPT !.pos = N - 1, !.counter = 0, !.color = "white"]
    /\ color' = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED <<active, pending, counter>>
    
Next ==
    \E n,m \in Node:
         \/ Terminate(n)
         \/ Wakeup(n)
         \/ SendMsg(n,m)
         \/ PassToken
         \/ InitiateToken
    
Constraint ==
    \A n \in Node: pending[n] < 4 /\ counter[n] \in -3..3

Safe ==
    \* IF terminationDetected THEN terminated ELSE TRUE
    [](terminationDetected => terminated)

ATD == INSTANCE AsyncTerminationDetection

ATDSpec == ATD!Spec

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(PassToken \/ InitiateToken)

THEOREM Implements == Spec => ATDSpec

-----------------------------------------------

Alias ==
    [
      active |-> active,
      counter |-> counter,
      color  |-> color,

      pending |-> pending,

      token  |->  token,

      t  |->  terminated,
      td  |-> terminationDetected       
    ]

-----------------------------------------------

\* \S 
SumF(func, from, to) ==
    LET sum[ n \in from..to ] ==
            IF n = from
            THEN func[n]
            ELSE func[n] + sum[n-1]
    IN IF from > to THEN 0 ELSE sum[to]

RECURSIVE Sum(_,_,_)
Sum(func, from, to) ==
    IF from > to THEN 0 ELSE func[from] + Sum(func, from+1, to)
    
\* SumF(func, from, to) ==
\*     Fold(+, func, 0, from..to)

\* B  to equal the sum of in-flight messages
B ==
    Sum(pending, 0, N-1)

t == token.pos
q == token.counter

 \* Inv == P0 /\ (P1 \/ P2 \/ P3 \/ P4)
 \*
 \* P0 == B = (Si: 0 <= i < N: counter[i])
 \* P1 == (\Ai: t < i < N: ~active[i]) /\ (Si: t < i < N: counter[i]) = q
 \* P2 == (\Si: 0 <= i <= t: counter[i]) + q > 0
 \* P3 == \Ei: 0 <= i <= t : color[i] = black
 \* P4 == The token.color = black
Inv ==
    /\ P0:: B = Sum(counter, 0, N-1)
    /\ \/ P1:: /\ \A n \in t+1 .. N-1: ~active[n] 
               /\ (Sum(counter, t+1, N-1) = q)
       \/ P2:: Sum(counter, 0, t) + q > 0       
       \/ P3:: \E n \in 0..t:  color[n] = "black"
       \/ P4:: token.color = "black" 


=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl
