It is time to pause and recap what we've done so far, both in terms of learning
TLA+ and modeling termination detection in a ring, a.k.a. EWD998.

Regarding the termination detection algorithm, checking the spec
 AsyncTerminationDetection   (with TLC and Apalache) confirms that the high-level
design of counting in-flight messages is a valid approach to detecting (global)
termination.  It might seem silly to write such a simple spec to confirm what is
easy to see is true.  On the other hand, writing a tiny spec is a small investment,
and "Writing is nature's way of letting you know how sloppy your thinking is"
(Guindon).  Later, we will see another reason why specifying
 AsyncTerminationDetection  paid off.

What comes next is to (re-)model  AsyncTerminationDetection  at a level of detail
that matches the EWD998 paper.  Here is a reformulated & reordered excerpt of the
eight rules that (informally) describe the algorithm:

0) Sending a message by node  i  increments a counter at  i  , the receipt of a
   message decrements i's counter
3) Receiving a *message* (not token) blackens the (receiver) node
2) An active node j -owning the token- keeps the token.  When j becomes inactive,
   it passes the token to its neighbor with  q = q + counter[j] 
4) A black node taints the token
7) Passing the token whitens the sender node
1) The initiator sends the token with a counter  q  initialized to  0  and color
   white
5) The initiator starts a new round iff the current round is inconclusive
6) The initiator whitens itself and the token when initiating a new round


Regarding learning TLA+, we've already covered lots of ground. Most importantly,
we encountered TLA with its temporal operators, behaviors, safety & liveness
properties, fairness, ...  Learning TLA+ is pretty much downhill from here on.

The remaining concepts this tutorial covers are:
- IF-THEN-ELSE
- Records
- Recursive functions & operators
- Refinement
- Tuples/Sequences
- CHOOSE operator (Hilbert's epsilon)

------------------------------- MODULE EWD998 -------------------------------
EXTENDS Integers \* No longer Naturals \* TODO Do you already see why?

CONSTANT 
    \* @type: Int;
    N

ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

Color == {"white", "black"}

VARIABLES 
    \* @type: Int -> Bool;
    active,
    \* @type: Int -> Int;
    pending,
    color,
    counter,
    token

vars == <<active, pending, color, counter, token>>

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ color \in [Node -> Color]
    /\ counter \in [Node -> Int]
    \* * TLA+ has records which are fuctions whose domain are strings. Since
     \* * records are functions, the syntax to create a record is that of a
     \* * function, except that the record key does not get quoted.
    \* * Finally, as with function sets we've seen earlier, it is easy
     \* * to define the set of records.  However, the syntax is not  ->  ,
     \* * but the  :  (colon),  [ a : {1,2,3} ]  .
    /\ token \in [ pos: Node, q: Int, color: Color ]

-----------------------------------------------------------------------------

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending = [i \in Node |-> 0]
    (* Rule 0 *)
    /\ color \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    /\ pending = [i \in Node |-> 0]
    /\ token = [pos |-> 0, q |-> 0, color |-> "black"]

-----------------------------------------------------------------------------

InitiateProbe ==
    (* Rules 1 + 5 + 6 *)
    /\ token.pos = 0
    /\ \* previous round inconclusive:
        \/ token.color = "black"
        \/ color[0] = "black"
        \/ counter[0] + token.q > 0
    /\ token' = [ pos |-> N-1, q |-> 0, color |-> "white"]
    /\ color' = [ color EXCEPT ![0] = "white" ]
    /\ UNCHANGED <<active, counter, pending>>                            

PassToken(i) ==
    (* Rules 2 + 4 + 7 *)
    /\ ~ active[i]
    /\ token.pos = i
    \* Rule 2 + 4
    \* Wow, TLA+ has an IF-THEN-ELSE expressions.
    \* TODO This could have been rewritten using  EXCEPT  .
    /\ token' = [ pos |-> i - 1, q |-> token.q + counter[i], 
        color |-> IF color[i] = "black" THEN "black" ELSE token.color ]
    \* Rule 7
    /\ color' = [ color EXCEPT ![i] = "white" ]
    /\ UNCHANGED <<>>

System ==
    \/ InitiateProbe
    \/ \E i \in Node \ {0}: PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ==
    (* Rule 0 *)
    /\ active[i]
    /\ UNCHANGED <<>>

\* Wakeup(i) in AsyncTerminationDetection.
RecvMsg(i) ==
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    (* Rule 0 + 3 *)
    /\ UNCHANGED <<>>

\* Terminate(i) in AsyncTerminationDetection.
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<pending, color, counter, token>>

Environment == 
    \E n \in Node:
        \/ SendMsg(n)
        \/ RecvMsg(n)
        \/ Deactivate(n)

-----------------------------------------------------------------------------

Next ==
  System \/ Environment

Spec == Init /\ [][Next]_vars

=============================================================================
