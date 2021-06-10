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
    \* CHOOSE  is almost always wrong when it appears in the behavior spec
     \* (except for constant-level operators such as  Min(S)  or when choosing
     \* what is called model-values).
     \* In TLA+, non-deteministic choice is expressed with existential
     \* quantification, like it was done in  Environment  and  System  .
     \* However, using  CHOOSE  is a common mistake, which is why this topic is
     \* covered in this tutorial.  CHOOSE  usually has the "advantage" to cause
     \* less state-space explosion; but not in a good way.
    /\ \E recv \in (Node \ {i}):
            pending' = [pending EXCEPT ![recv] = @ + 1]
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
Deactivate ==
    \* Modeling variant: Let multiple (logical processes) nodes deactivate at
     \* the same time/in the same step. This breaks the refinement ATD => STD.
     \* (Pick a function from the set of functions s.t. the inactive nodes in
     \* the current step remain inactive and the active nodes in the current
     \* step non-deterministically deactivate.)
    /\ active' \in { f \in [ Node -> BOOLEAN] : \A n \in Node: ~active[n] => ~f[n] }
    \* To avoid generating behaviors that quickly stutter when simulating the spec.
    \* /\ active' # active
    /\ UNCHANGED <<pending, color, counter, token>>

Environment == 
    \E n \in Node:
        \/ SendMsg(n)
        \/ RecvMsg(n)
        \/ Deactivate

-----------------------------------------------------------------------------

Next ==
  System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)
\* With the refinement below, TLC produces the following (liveness) violation:
 \* Error: Temporal properties were violated.
 \*
 \* Error: The following behavior constitutes a counter-example:
 \*
 \* State 1: <Initial predicate>
 \* /\ pending = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
 \* /\ counter = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
 \* /\ token = [q |-> 0, color |-> "black", pos |-> 0]
 \* /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
 \* /\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white")
 \*
 \* State 2: <InitiateProbe line 93, col 5 to line 100, col 45 of module EWD998>
 \* /\ pending = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
 \* /\ counter = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
 \* /\ token = [q |-> 0, color |-> "white", pos |-> 2]
 \* /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
 \* /\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white")
 \*
 \* State 3: <PassToken line 104, col 5 to line 113, col 45 of module EWD998>
 \* /\ pending = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
 \* /\ counter = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
 \* /\ token = [q |-> 0, color |-> "white", pos |-> 1]
 \* /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
 \* /\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white")
 \*
 \* State 4: Stuttering
\* This counter-examples makes us realize that we haven't defined a suitable
 \* fairness property for  EWD998 .
\* With  WF_vars(Next)  , TLC finds a counter-example where the  Initiator  
 \* forever initiates new token rounds, but one node never receives a message
 \* that was send to it.
 \*
 \* State 1: <Initial predicate>
 \* /\ pending = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
 \* /\ counter = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
 \* /\ token = [q |-> 0, color |-> "black", pos |-> 0]
 \* /\ active = (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE)
 \* /\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white") 
 \*
 \* State 2: <SendMsg line 123, col 5 to line 132, col 41 of module EWD998>
 \* /\ pending = (0 :> 0 @@ 1 :> 1 @@ 2 :> 0)
 \* /\ counter = (0 :> 1 @@ 1 :> 0 @@ 2 :> 0)
 \* /\ token = [q |-> 0, color |-> "black", pos |-> 0]
 \* /\ active = (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE)
 \* /\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white")
 \*
 \* State 3: <InitiateProbe line 93, col 5 to line 100, col 45 of module EWD998>
 \* /\ pending = (0 :> 0 @@ 1 :> 1 @@ 2 :> 0)
 \* /\ counter = (0 :> 1 @@ 1 :> 0 @@ 2 :> 0)
 \* /\ token = [q |-> 0, color |-> "white", pos |-> 2]
 \* /\ active = (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE)
 \* /\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white")
 \*
 \* State 4: <PassToken line 104, col 5 to line 113, col 45 of module EWD998>
 \* /\ pending = (0 :> 0 @@ 1 :> 1 @@ 2 :> 0)
 \* /\ counter = (0 :> 1 @@ 1 :> 0 @@ 2 :> 0)
 \* /\ token = [q |-> 0, color |-> "white", pos |-> 1]
 \* /\ active = (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE)
 \* /\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white")
 \*
 \* State 5: <PassToken line 104, col 5 to line 113, col 45 of module EWD998>
 \* /\ pending = (0 :> 0 @@ 1 :> 1 @@ 2 :> 0)
 \* /\ counter = (0 :> 1 @@ 1 :> 0 @@ 2 :> 0)
 \* /\ token = [q |-> 0, color |-> "white", pos |-> 0]
 \* /\ active = (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE)
 \* /\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white")
 \*
 \* Back to state 3: <InitiateProbe line 93, col 5 to line 100, col 45 of module EWD998>
 \*
 \* This hints at the fact that  EWD998  does not handle unreliable message
 \* delivery.  However, what is really happening is that the  RecvMsg  never
 \* occurs.  How can that be, since we defined (weak) fairness on the  Next  
 \* action and its sub-action  RecvMsg  is permanently enabled?
 \* Fairness does not distribute over the sub-actions of an action such as  Next  .
 \* If this is what we want, we would have to conjoin multiple fairness 
 \* conditions to  Spec  ; one for each sub-action.  This isn't really what we
 \* want, though.  Fundamentally, the algorithm described in EWD998 detects
 \* termination if and only if all nodes (eventually) terminate.  If the nodes
 \* never terminate (which subsumes sending messages back and forth), there is
 \* no termination to detect.  This suggests that we are only interest in
 \* checking whether or not termination is detected for those behaviors where
 \* all nodes eventually terminate.

terminationDetected ==
    /\ token.pos = 0
    /\ token.color = "white"
    /\ token.q + counter[0] = 0
    /\ color[0] = "white"
    /\ ~ active[0]

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
ATD == INSTANCE AsyncTerminationDetection

THEOREM Implements == Spec => ATD!Spec

\* The bang is not a valid token in a config file.
ATDSpec == ATD!Spec

\* With the refinement done, it is sanity-check time again. As we have learned
 \* with the state constraint earlier, a good check is to quickly generate a
 \* small number of behaviors.  If some actions are not covered, we have to look
 \* closer.
\* Another useful sanity-check is to verify the spec for a single node, i.e., 
 \*  N = 1  .  We want termination to detect termination of a single node, no?
\* Generating the graph with "full" statistics reveals the context in which the
 \* action formulae are evaluated.  In other words, the graph includes the
 \* parameters that were "passed" to the actions.
 \* For the graph generated from EWD998, the  RecvMsg  action for the context
 \*  [i->2]  , which corresponds to node #2 is not covered.  This means that the
 \* sub-action  RecvMsg  was never enabled when the simulator generated the
 \* behaviors, which can be the case iff  SendMsg   never incremented
 \*  pending[2]  . This might just be exceptional luck, but maybe there is
 \* something more subtle going on.  This is an excellent opportunity to meet
 \* the TLA+ debugger (that has recently been added :-).

-----------------------------------------------------------------------------

HasToken ==
    token.pos

\* Usually, one would find additional invariants and liveness properties at this
 \* stage and check the spec for different spec parameters.  The second part can
 \* easily be parallelized and scaled out (hello cloud computing!).
\* If higher assurances are needed, now would be the start of proving  EWD998
 \* correct, which requires finding an inductive invariant.  Finding an
 \* inductive invariant is hard because one has to know *why* the algorithm
 \* works (model-checking only confirms that algorithms work according to the
 \* checked properties).
\* Fortunately, the EWD998 paper gives an inductive invariant in the form of a
 \* larger formula  P0 /\ (P1 \/ P2 \/ P3 \/ P4)  , with  \S  representing
 \* "the sum of",  B  to equal the sum of in-flight messages,  and  P0  to  P4 : 
 \*
 \* P0: B = Si: 0 <= i < N: c.i)
 \* P1: (Ai: t < i < N: machine nr.i is passive) /\
 \*     (Si: t < i < N: c.i) = q
 \* P2: (Si: 0 <= i <= t: c.i) + q > 0
 \* P3: Ei: 0 <= i <= t : machine nr.i is black
 \* P4: The token is black

\* TLA doesn't have for loops with which we could sum the elements of the 
 \* variables  counter  and  pending  ; TLA+ is not an imperative programming
 \* language.  Instead, TLA+ has recursive functions.  We could write a
 \* function to sum the variable  counter  as:
 \* 
 \*  SumC == CHOOSE f : f = [ i \in 0..N-1 |-> IF i = 0 
 \*                                            THEN counter[i]
 \*                                            ELSE f[i-1] + counter[i]  ]
 \* 
 \* The sum of  counter  would then be  SumC[N-1]  .
 \* TLC does not evaluate unbounded choose.  However, TLA+ has a syntactic
 \* variant that TLC evaluates:
 \* 
 \*  SumC[ i \in 0..N-1 ] == IF i=0 THEN counter[i] ELSE SumC[i-1] + counter[i]
 \*
 \* To write a recursive function to sum the elements of a function given a
 \* (subset) of its domain that is independent of  counter  , and, thus, also
 \* works for  pending  , we need to see another TLA+ concept.  A let/in
 \* expression allows us to use locally define operators. A let/in is just a
 \* syntactic concept, and the expression is equivalent to an expression
 \* with all locally defined operators in-lined.
\* @type: (Int -> Int, Int, Int) => Int;
\* Sum(fun, from, to) ==
\*     LET sum[ i \in from..to ] ==
\*             IF i = from THEN fun[i]
\*             ELSE sum[i-1] + fun[i]
\*     IN sum[to]

\* Alternatively, one can write recursive operators. What distinguishes a
 \* recursive operator from an ordinary operator, is a  RECURSIVE  operator
 \* declaration.
 \* Compared to recursive functions, TLC usually evaluate recursive operators
 \* faster.  However, that is not the case for Apalache.  PlusPy, a tool to
 \* execute TLA+ specifications, doesn't support recursive operators at all.
\* Commented because of https://git.io/JGAf7 and mandatory bounds for unrolling
\* https://apalache.informal.systems/docs/apalache/principles.html#recursion
\* RECURSIVE SumO(_,_,_)
\* SumO(fun, from, to) ==
\*     IF from = to 
\*     THEN fun[to]
\*     ELSE fun[from] + SumO(fun, from+1, to)

\* Lastly, we can re-use fold operators from the TLA+ CommunityModules at
 \* https://github.com/tlaplus/CommunityModules that are especially well-known
 \* among functional programmers.  This gives us a chance to show  LAMBDA  
 \* in TLA+.
\* Commented because of https://git.io/JGAf7 and lack of annotations in Utils.tla
Sum(fun, from, to) ==
    LET F == INSTANCE Functions
    IN F!FoldFunctionOnSet(LAMBDA a,b: a+b, 0, fun, from..to)

B ==
    \* This spec counts the in-flight messages in the variable  pending  .
    Sum(pending, 0, N-1)

Inv == 
    /\ P0:: B = Sum(counter, 0, N-1)
    /\  \/ P1:: /\ \A i \in (token.pos+1)..N-1: ~ active[i]
            /\ IF token.pos = N-1 
               THEN token.q = 0 
               ELSE token.q = Sum(counter, (token.pos+1), N-1)
        \/ P2:: Sum(counter, 0, token.pos) + token.q > 0
        \/ P3:: \E i \in 0..token.pos : color[i] = "black"
        \/ P4:: token.color = "black"

\* We expect that  Inv  is an inductive invariant that we can eventually prove
 \* correct with TLAPS.  However, "it is easier to prove something if it's true",
 \* and, thus, we validate  IInv  for small values of  N  with model-checking.
 \* For that, we conjoin  TypeOK  with  Inv  to  IInv  , and (logically) check
 \* the formula with TLC:
 \*
 \*  IInv /\ [Next]_vars => IInv'
 \*
IInv ==
    /\ TypeOK
    /\ Inv

=============================================================================
