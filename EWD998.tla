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
    /\ token' = [ token EXCEPT !.pos = @ - 1,
                               !.q   = @ + counter[i],
                               !.color = IF color[i] = "black" THEN "black" ELSE @ ]
    \* Rule 7
    /\ color' = [ color EXCEPT ![i] = "white" ]
    /\ UNCHANGED <<active, pending, counter>>

System ==
    \/ InitiateProbe
    \/ \E i \in Node \ {0}: PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ==
    (* Rule 0 *)
    /\ active[i]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    \* TLA has a CHOOSE operator that picks a value satisfying some property:  
     \*   CHOOSE x \in S: P(x)   
     \* The choice is deterministic, meaning that CHOOSE always picks the same value.
     \* If no value in  S  satisfies the property  P  , the value of the CHOOSE
     \* expression is undefined.  It is *not* an error in TLA, although TLC will
     \* complain. Likewise, TLC won't choose if  S  is unbound/infinite.
    /\ pending' = [pending EXCEPT ![ (CHOOSE j \in Node : j # i) ] = @ + 1]
    /\ UNCHANGED <<active, color, token>>

\* Wakeup(i) in AsyncTerminationDetection.
RecvMsg(i) ==
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    (* Rule 0 + 3 *)
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ color' = [ color EXCEPT ![i] = "black" ]
    /\ UNCHANGED <<token>>

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

\* We haven't checked anything except the  TypeOK  invariant above, which does
 \* not say anything about termination detection.  What we could do, is to
 \* re-state and check the same theorems  Stable  and  Live  that we checked for
 \*  AsyncTerminationDetection  -- copy&paste is acceptable with specs after all!
 \* On the other hand, this is not exactly what we want to check; we don't want
 \* to check that (an amended)  Stable  and  Live  hold for  EWD998.  What we
 \* really care about is that the module  EWD998  *implements* the high-level
 \* specificiation  AsyncTerminationDetection  (ATD).
 \* With TLA, implementation is (logical) implication.  To state that some spec
 \*  I  implements  a higher-level specification  A  is formally expressed as
 \*  I => A  .  This is  equivalent to saying that the behaviors defined by  I
 \* are a subset of the behaviors defined by  A  .  However, what if  I  declares
 \* additional variables that don't exist in  A  ?  For spec  EWD998  , the
 \* variables  color, token, pending  do not appear in  ATD  .  This is where
 \* the sub-scripts we added to the various temporal formulas in  ATD  start to
 \* make sense.  Recall that  [][A]_v  is equivalent to  [](A \/ v'=v)  .  This
 \* formula is true of behaviors in which variables - not appearing in  [A]_v  -
 \* change in any way they want, as long as the variables in  v  remain unchanged,
 \* or a  A step happens.  In fact,  [A]_v  does not say anything about variables
 \* not appearing in it; the formula does not "care" about those variables.  For
 \*  EWD998  and  ATD  ,  the module  ATD  allows the module  EWD998  to specify
 \* anything "in line" with  ATD  .
 \* Remember that an  A  step  above is just an action-level formula.  The
 \* identifier  A  of its definition is just a syntactic element to make specs
 \* more readable.  In other words, when we say  A  step above, we talk about
 \* the formula (the right-hand side of  A == foo).  Thus, the  A  step of  ATD
 \* can be a  B  step of  EWD998  provided that  B  is a step permitted by  A  .
\* This theorem is syntactically incorrect, because we haven't added the module
 \*  AsyncTerminationDetection  to the list of  EXTENDS  at the top of  EWD998.
 \* If we were to add  ATD  to the  EXTENDS  , we would end up with various name
 \* clashes.  Think of  EXTENDS  as inlining the extended modulese.
 \* What we need is to "import"  ATD  under a new namespace, thoug.  In TLA, the
 \* term is instantiation, syntactically expressed with  INSTANCE M  where  M  
 \* is a module.  To instantiate module  M  into a namespace, we rely on the
 \* (fundamental) concept of definitions again:  M == INSTANCE M  .
\* The module  ATD  declares the variables  terminationDetected  that is absent
 \* in  EWD998  .  In other words,  EWD998  does not define a value of the
 \* variable  terminationDetected  in its behaviors.  We can define the value of
 \*  terminationDetected  in  EWD998  by stating with what expression  
 \*  terminationDetected  should be substituted that is equivalent to  
 \*  ATD!terminationDetected  .  Syntactically, we append a
 \*  WITH symbol <- substitution  to the INSTANCE statement.
\* TODO Will it work if we substitute  terminationDetected  with  TRUE  ?  Find
 \* TODO out, but don't forget to have TLC check this property.
ATD == INSTANCE AsyncTerminationDetection WITH terminationDetected <- TRUE

THEOREM Implements == Spec => ATD!Spec
-----------------------------------------------------------------------------

HasToken ==
    token.pos

=============================================================================
