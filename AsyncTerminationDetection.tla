---------------------- MODULE AsyncTerminationDetection ---------------------
\* * TLA+ is an expressive language and we usually define operators on-the-fly.
 \* * That said, the TLA+ reference guide "Specifying Systems" (download from:
 \* * https://lamport.azurewebsites.net/tla/book.html) defines a handful of
 \* * standard modules.  Additionally, a community-driven repository has been
 \* * collecting more modules (http://modules.tlapl.us). In our spec, we are
 \* * going to need operators for natural numbers.
EXTENDS Naturals

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
  pending,              \* number of messages pending at a node
  \* * Up to now, this specification didn't teach us anything useful regarding
   \* * termination detection in a ring (we were mostly concerned with TLA+ itself).
   \* * Let's change this to find out if this proto-algorithm detects termination.
   \* * In an implementation, we could write to a log file whenever the system
   \* * terminates.  However, for larger systems it can be challenging to collect
   \* * e.g., a consistent snapshot.  In a spec, we can just use an (ordinary) variable
   \* * that -contrary to the other variables- doesn't define the state the system is
   \* * in, but records what the system has done so far.  The jargon for this variable
   \* * is "history variable".
   \* * For termination detection, the complete history of the computation, performed
   \* * by the system, is not relevant--we only care if the system detected
   \* * termination.
  terminationDetected

\* * A definition that lets us refer to the spec's variables (more on it later).
vars == << active, pending, terminationDetected >>

terminated == \A n \in Node : ~ active[n] /\ pending[n] = 0

-----------------------------------------------------------------------------

\* * Initially, all nodes are active and no messages are pending.
Init ==
    \* * ...all nodes are active.
     \* * The TLA+ language construct below is a function. A function has a domain
     \* * and a co-domain/range. Lamport: ["In the absence of types, I don't know
     \* * what a partial function would be or why it would be useful."]
     \* * (http://discuss.tlapl.us/msg01536.html).
     \* * Here, we "map" each element in Node to the value TRUE (it is just
     \* * coincidence that the elements of Node are 0, 1, ..., N-1, which could
     \* * suggest that functions are just zero-indexed arrays found in programming
     \* * languages. As a matter of fact, the domain of a function can be any set,
     \* * even infinite ones: [n \in Nat |-> n]).
    \* * /\ is logical And (&& in programming). Conjunct lists usually make it easier
     \* * to read. However, indentation is significant!
    \* * So far, the initial predicate defined a single state.  That seems natural as
     \* * most programs usually start with all variables initialized to some fixed
     \* * value.  In a spec, we don't have to be this strict.  Instead, why not let
     \* * the system start from any (type-correct) state?
     \* * Besides syntax to define a specific function, TLA+ also has syntax to define
     \* * a set of functions mapping from some set S (the domain) to some other set T:
     \* *   [ S -> T ] or, more concretely:  [ {0,1,2,3} -> {TRUE, FALSE} ]
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> Nat ]
    /\ terminationDetected \in {FALSE, terminated}

\* * Recall that TLA+ is untyped and that we are "free" to write silly expressions.  So
 \* * why no types?  The reason is that, while real-world specs can be big enough for 
 \* * silly expressions to sneak in (still way smaller than programs), types would 
 \* * unnecessarily slow us down when specifying (prototyping). Also, there is a way to
 \* * catch silly expressions quickly.
\* * It's finally time to state and check a first correctness property, namely that our
 \* * spec is "properly typed".  We do this by writing an operator that evaluates to
 \* * false, should values of variables not be as expected.  We can think of this a
 \* * stating the types of variables in a special place, and not where they are declared
 \* * or where values are assigned.  When TLC verifies the spec, it will evaluate the
 \* * operator on every state it generates.  If the operator evaluates to false, an error
 \* * is reported.  In other words, the operator is an invariant of the system.
 \* * Invariants are (a class of) safety properties, and safety props are "informally"
 \* * define as "nothing bad ever happens" (a formal definition can be found in
 \* * https://link.springer.com/article/10.1007/BF01782772, but we won't need it).
TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> Nat ]
    /\ terminationDetected \in BOOLEAN 

-----------------------------------------------------------------------------

\* * Each one of the definitions below represent atomic transitions, i.e., define
 \* * the next state of the current behavior (a state is an assignment of
 \* * values to variables). We call those definitions "actions". A next state is
 \* * possible if the action is true for some combination of current and next
 \* * values. Two or more actions do *not* happen simultaneously; if we want to
 \* * e.g. model things to happen at two nodes at once, we are free to choose an
 \* * appropriate level of granularity for those actions.

\* * Node i terminates.
Terminate(i) ==
    \* * Assuming active is a function (can we be sure?), function application
     \* * is denoted by square brakets.  A mathmatician would expect parens, but TLA+
     \* * uses parenthesis for (non-zero-arity) operator application.
    \* * If node i is active *in this state*, it can terminate...
    /\ active[i]
    \* * ...in the next state (the prime operator ').
    \* * The previous expression didn't say anything about the other values of the
     \* * function, or even state that active' is a function (function update).
    /\ active' = [ active EXCEPT ![i] = FALSE ]
    \* * Also, the variable active is no longer unchanged.
    /\ pending' = pending
    \* * Possibly (but not necessarily) detect termination, iff all nodes are inactive
     \* * and no messages are in-flight.
    /\ terminationDetected' \in {terminationDetected, terminated'}

\* * Node i sends a message to node j.
SendMsg(i, j) ==
    /\ active[i]
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED << active, terminationDetected >>

\* * Node I receives a message.
Wakeup(i) ==
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ UNCHANGED << terminationDetected >>

DetectTermination ==
    /\ terminated
    /\ ~terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED << active, pending >>

-----------------------------------------------------------------------------

\* * Here we define the complete next-state action. Recall that it’s a predicate
 \* * on two states — the current and the next — which is true if the next state
 \* * is acceptable.
 \* * The next-state relation should somehow plug concrete values into the 
 \* * (sub-) actions Terminate, SendMsg, and Wakeup.
Next ==
    \/ DetectTermination
    \/ \E i,j \in Node:   
        \/ Terminate(i)
        \/ Wakeup(i)
        \* ? Is it correct to let node i send a message to node j with i = j?
        \/ SendMsg(i, j)

Stable ==
    \* * With the addition of the auxiliary variable  terminationDetected  and
     \* * the action  DetectTermination  , we can check that our (ultra) high-level
     \* * design achieves termination detection.
    \* * Holds iff  tD = FALSE  instead of    in  Init/MCInit.
     \* * If the definition of  MCInit  in MCAsyncTerminationDetection.tla is
     \* * changed to  terminationDetected \in {FALSE, terminated}  ,  Stable  
     \* * is violated by the initial state:
     \* *    Error: Property Stable is violated by the initial state:
     \* *    /\ pending = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
     \* *    /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
     \* *    /\ terminationDetected = FALSE
     \* * Why? Because  Stable  just asserts something about initial states.
     \* * With  terminationDetected \in {FALSE, terminated}  , the state above
     \* * becomes an initial state (see Specifying Systems p. 241 for morew details).
    \* * How do we say that we want  Stable  to hold for all states of a behavior,
     \* * not just for initial states?  In other words, how do we state properties
     \* * that are evaluated on behaviors; not just single states?
     \* * We have arrived at the provenance of temporal logic.  There are many temporal
     \* * logics, and TLA is but one of them (the missing "+" is not a typo!).
     \* * Like with programming, different (temporal) logics make different tradeoffs.
     \* * Compared to, e.g., Linear temporal logic (LTL), TLA has the two (fundamental)
     \* * temporal operators, Always (denoted as [] and pronounced "box") and Eventually
     \* * (<> pronounced "diamond"). In contrast, LTL has Next and Until, which means
     \* * that one cannot say the same things with both logics.  TLA's operators
     \* * guarantee that temporal formulae are stuttering invariant, which we will touch
     \* * on later when we talk about refinement.
     \* * For now, we just need the Always operator, to state  Stable.   []Stable asserts
     \* * that  Stable  holds in all states of a behavior.  In other words, the formula
     \* * Stable is always true.  Note that Box can also be pushed into the definition of
     \* * Stable.
    \* * The following behavior violates the (strengthened)  Stable:
     \* *    State 1: <Initial predicate>
     \* *    /\ pending = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
     \* *    /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE)
     \* *    /\ terminationDetected = FALSE
     \* *    State 2: <Terminate line 122, col 5 to line 131, col 66 of module AsyncTerminationDetection>
     \* *    /\ pending = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
     \* *    /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
     \* *    /\ terminationDetected = FALSE
     \* *    State 3: <DetectTermination line 147, col 5 to line 149, col 38 of module AsyncTerminationDetection>
     \* *    /\ pending = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
     \* *    /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
     \* *    /\ terminationDetected = TRUE
     \* *    State 4: Stuttering
     \* * Have we already found a flaw in our design and are forced back to the
     \* * whiteboard?  No, you (intentionally) got hold of the wrong end of the stick.
     \* * It is not that  terminated  implies  terminationDetection  , but the other
     \* * way around.
    \* * Phew, we have a high-level design (and you learned a lot about TLA+). Let's
     \* * move to the next level.  Except, one should always be suspicious of success...
    [](terminationDetected => []terminated)

-----------------------------------------------------------------------------

\* * It is usually a good idea to check a couple of non-properties, i.e., properties that
 \* * we expect to be violated.  We will use the behavior that violates the non-property
 \* * as a sanity check.
 \* * So far, our spec has  TypeOK  that assert the "types" of the variables and  Stable
 \* * that asserts that   terminationDetected  can only be true, iff  terminated  is true.
 \* * In TLA, we can also assert that (sub-)actions occur in a behavior; after all, it's
 \* * the Temporal Logic of *Actions*.  :-)  A formula,  [A]_v  with  A  an action holds
 \* * for a behavior if ever step (pair of states) is an  [A]_v  step.  For the moment,
 \* * we will ignore the subscript  _v  and simply write  _vars instead of it:  [A]_vars.
 \* *
ActuallyNext ==
    [][DetectTermination \/ \E i,j \in Node: (Terminate(i) \/ Wakeup(i) \/ SendMsg(i,j))]_vars
    \* * In hindsight, it was to be expected that the trace just has two states
     \* * i.e., a single step.  The property  OnlyTerminating  is violated by
     \* * behaviors that take our actions:
     \* *    Error: Action property OnlyTerminating is violated.
     \* *    Error: The behavior up to this point is:
     \* *    State 1: <Initial predicate>
     \* *    /\ pending = (0 :> 1 @@ 1 :> 1 @@ 2 :> 1)
     \* *    /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
     \* *    /\ terminationDetected = FALSE
     \* *    
     \* *    State 2: <Wakeup line 141, col 5 to line 144, col 42 of module AsyncTerminationDetection>
     \* *    /\ pending = (0 :> 0 @@ 1 :> 1 @@ 2 :> 1)
     \* *    /\ active = (0 :> TRUE @@ 1 :> FALSE @@ 2 :> FALSE)
     \* *    /\ terminationDetected = FALSE
    \* * Let's now focus on the subscript  _v  part that we glossed over previously.
     \* * The subscript  _v  in  [A]_v  is a state-function, a formula without action- or
     \* * temporal-level operators, that -informally- defines what happens with the
     \* * variables. 
     \* * We replaced  _v  with  _vars  where  vars  equals the defintion on line 57
     \* *  << active, pending, terminationDetected >>  .  Note that  << >>  is just syntactic
     \* * sugar to conveniently state  1-indexed arrays.  However, they are called 
     \* * sequences in TLA are many useful sequence-related operators are defined in the
     \* * Sequences.tla standard module.  More importantly, a sequence has an order!
     \* * Time to pull out the TLA+ cheat sheet and check page 4:
     \* *  https://www.hpl.hp.com/techreports/Compaq-DEC/SRC-TN-1997-006A.pdf
    \* * The formula  [A]_v  is equivalent to  A \/ (v' = v)  .  Semantically, every
     \* * step of the behavior is an  A  step, or the variables in  v  remain unchanged.
    \* * If you look closely, you will realize that the disjunct of actions nested in
     \* *  OnlyTerminating  is equivalent to the  Next  operator above!  Up to now,
     \* * we've been using a TLC feature that lets us pass  INIT  and  NEXT  in TLC's
     \* * configuration file.  In TLA, the system specification that defines the set of
     \* * of valid system behaviors, is actually given as a temporal formula.

F ==
    \* * With this liveness property  F  , all (other) properties hold. :-)  However,
     \* * it looks funny that check  Live1  and  Live2  when both are also part of  Spec.
     \* * At the level of termination detection with EWD998,  terminated  might never be
     \* * true because nodes may never terminate.
     \* * Additionally, there is a second problem with  F  that is even independent of
     \* * EWD998: A scheduler would have to look into the future to see if the
     \* * scheduling choice it is making at some point, leads to an unrecoverable state
     \* * later from where the stipulated "good thing" can no longer happen.  This is
     \* * elsewhere informally called "paint itself in the corner", or -formally- is the
     \* * topic of machine-closed specifications.
    \* * We want  F  to not add additional safety properties on top of  Spec  .  We won't
     \* * discuss the whys here, but if we restrict ourselve to only stipulate that
     \* * enabled sub-actions of the next-state relation  Next  eventually happen, we can
     \* * be sure that we don't paint the scheduler in the corner.  To rule out the
     \* * behavior shown by TLC as a violation of  Live1  , we have to require that a
     \* * Next  step eventually hapens (if it is "possible"). We need to put a number of
     \* * previously seen concepts together now:
     \* * - =>  (implication)
     \* * - ENABLED
     \* * - <<A>>_v
     \* * - Combining  []  and  <>  to  []<>  and  <>[]
     \* * "If  A  is enabled forever,  infinitely many  A  steps will eventually occur."
     \* *   <>[](ENABLED <<Next>>_vars) => []<><<Next>>_vars
     \* * This can be written more compactly as  WF_vars(Next)  , but TLC still shows
     \* * a lasso-shaped counter-example:
     \* *   
     \* *   Error: Temporal properties were violated.
     \* *   
     \* *   Error: The following behavior constitutes a counter-example:
     \* *   
     \* *   State 1: <Initial predicate>
     \* *   /\ pending = (0 :> 1 @@ 1 :> 1 @@ 2 :> 1)
     \* *   /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
     \* *   /\ terminationDetected = FALSE
     \* *   
     \* *   State 2: <Wakeup line 141, col 5 to line 144, col 42 of module AsyncTerminationDetection>
     \* *   /\ pending = (0 :> 1 @@ 1 :> 1 @@ 2 :> 0)
     \* *   /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE)
     \* *   /\ terminationDetected = FALSE
     \* *   
     \* *   State 3: <SendMsg line 135, col 5 to line 137, col 50 of module AsyncTerminationDetection>
     \* *   /\ pending = (0 :> 1 @@ 1 :> 1 @@ 2 :> 1)
     \* *   /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE)
     \* *   /\ terminationDetected = FALSE
     \* *   
     \* *   Back to state 1: <Terminate line 122, col 5 to line 131, col 66 of module AsyncTerminationDetection>
    \* TODO Do we have to conjoin  WF_vars(Next)  with additional fairness properties to
     \* TODO make  Live1  and  Live2  hold?
    WF_vars(Next)

\* * We’ll now define a formula that encompasses our specification of how the system
 \* * behaves. It combines the Initial state predicate, the next-state action, and
 \* * something called a fairness property that we will learn about later.
 \* * It is convention to name the behavior spec  Spec  .
Spec ==
    Init /\ [][Next]_vars /\ F

Terminates ==
    \* * The behavior spec  Spec  asserts that every step/transition is a  Next  step, or
     \* * the variables do not change.  But is it actually true that the system can always
     \* * and forever take a  Next  step?  Semantically, we are specifying termination
     \* * detection.  Does the algorithm for termination detection itself terminate or can
     \* * it execute forever?
    \* * TLA defines an  ENABLED  operator with which we can state predicates such as
     \* *  ENABLED A  .  This prediacte is true iff action A is enabled, i.e., there exists
     \* * a state  t  such that the transition  s -> t  is an A step.
    []ENABLED [Next]_vars
    

\* * In  Terminates  , we asserted that it is always "possible" to take a  Next  step, or that
 \* * it is possible for all variables to remain unchange:  Next \/ vars' = vars  .  This is
 \* * a tautology in  TLA  and we effectively checked  that  Spec => TRUE  .  A related mistake
 \* * is when the antecedent is  FALSE  :  FALSE => TRUE  (Try conjoining 1 = 2 to  Spec )
 \* * Remember:  [](Be suspicious of success).
 \* *
 \* * Sometime, we wish to assert that all or some steps are an  A  step (for an action A),
 \* * and some variables change. In other words, we wish to assert  A /\ vars' # vars  (which
 \* * is equivalent to   ~(~A \/ vars' = vars)  ).  TLA has dedicated syntax for this, which
 \* * is  <<A>>_v   where  v  is usually  vars  but can be any state function.
AngleNextSubVars ==
    []ENABLED <<Next>>_vars

-----------------------------------------------------------------------------

Live1 ==
    \* * Up to now, we have been stating safety properties, i.e., "nothing bad ever happens".
     \* * Looking at the counter-examples we've encountered so far, we find that a safety
     \* * property is a finite prefix of a (infinite) behavior where the final state or action
     \* * (transition) violates the property.  We primarily care about safety when we check
     \* * systems.  For example, when we (used to) board a plane, we very much care that the
     \* * plane never crashes!  However, if the pilots decide not to take off, the plane is
     \* * guaranteed not to crash.  So we sit on the plane forever, waiting for it to depart.
     \* * Clearly, as travelers, we eventually wish to arrive at our destination, e.g., to
     \* * attend a meeting next Tuesday.  Can we formulate this as a safety property?  Easy,
     \* * if we assume a (global) clock that determines when it is Tuesday.  Specifying
     \* * algorithms or systems, we know how to replicate clocks. However, an algorithm that
     \* * requires something to happen in a fixed amount of (some notion of) time is brittle.
     \* * For example, an algorithm that counts hardware instructions will likely only work
     \* * on a particular hardware architecture. For EWD998, we could assert that termination
     \* * is detected within N rounds after termination occurred, but do we know the value of
     \* * N?  And even with an N, we would need another property to assert that each round
     \* * terminates...
     \* * A way out is to formulate the property such that we assert that "something good 
     \* * eventually happens"--the plane eventually arrives at its destination; the algorithm
     \* * eventually produces a result, termination is eventually detected.
     \* *
     \* * Requiring something good to eventually happen is a liveness property. Unfortunately,
     \* * in practice, it is not very useful to know that the algorithm eventually produces a
     \* * result if it takes 5 billion years to do so.
     \* *
     \* * A violation of a liveness property is -contrary to a safety property- an infinite
     \* * behavior where the "good thing" never happens.  When printed, tools such as TLC show
     \* * a lasso where the property doesn't hold in the lasso loop.
     \* *
     \* * In TLA, we syntactically express a property that asserts that something good
     \* * eventually happens, with the diamond operator  <>  (which is just the dual of the box
     \* * operator:  <>P <=> ~[]~P  ).
    \* * 
     \* *   Error: Temporal properties were violated.
     \* *   Error: The following behavior constitutes a counter-example:
     \* *   State 1: <Initial predicate>
     \* *   /\ pending = (0 :> 1 @@ 1 :> 1 @@ 2 :> 1)
     \* *   /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
     \* *   /\ terminationDetected = FALSE
     \* *   State 2: Stuttering
    <>terminated

Live2 ==
    \* *    Error: The following behavior constitutes a counter-example:
     \* *   State 1: <Initial predicate>
     \* *   /\ pending = (0 :> 1 @@ 1 :> 1 @@ 2 :> 1)
     \* *   /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
     \* *   /\ terminationDetected = FALSE
     \* *   State 2: <Wakeup line 141, col 5 to line 144, col 42 of module AsyncTerminationDetection>
     \* *   /\ pending = (0 :> 1 @@ 1 :> 1 @@ 2 :> 0)
     \* *   /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE)
     \* *   /\ terminationDetected = FALSE
     \* *   State 3: <Wakeup line 141, col 5 to line 144, col 42 of module AsyncTerminationDetection>
     \* *   /\ pending = (0 :> 0 @@ 1 :> 1 @@ 2 :> 0)
     \* *   /\ active = (0 :> TRUE @@ 1 :> FALSE @@ 2 :> TRUE)
     \* *   /\ terminationDetected = FALSE
     \* *   State 4: <Terminate line 122, col 5 to line 131, col 66 of module AsyncTerminationDetection>
     \* *   /\ pending = (0 :> 0 @@ 1 :> 1 @@ 2 :> 0)
     \* *   /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE)
     \* *   /\ terminationDetected = FALSE
     \* *   State 5: <Wakeup line 141, col 5 to line 144, col 42 of module AsyncTerminationDetection>
     \* *   /\ pending = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
     \* *   /\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE)
     \* *   /\ terminationDetected = FALSE
     \* *   State 6: <Terminate line 122, col 5 to line 131, col 66 of module AsyncTerminationDetection>
     \* *   /\ pending = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
     \* *   /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE)
     \* *   /\ terminationDetected = FALSE
     \* *   State 7: <Terminate line 122, col 5 to line 131, col 66 of module AsyncTerminationDetection>
     \* *   /\ pending = (0 :> 0 @@ 1 :> 0 @@ 2 :> 0)
     \* *   /\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)
     \* *   /\ terminationDetected = FALSE
     \* *   State 8: Stuttering
    <>terminationDetected

    \* * For both properties  Live1  and  Live2  ,  TLC reports counter-examples that end in
     \* * stuttering.  This is strange!  Clearly, the counter-example for  Live1  could be
     \* * extended by, e.g., a  Wakeup  action that "consumes" one of the pending messages.
     \* * Similarly, the counter-example for  Live2  could be extended by a
     \* *  DetectTermination action.
     \* * We have to look at  Spec  again to see what is happening.  The (temporal) formula
     \* *  Spec  defines a set of behaviors, and this set includes the counter-examples
     \* * reported for  Live1  and  Live2  .  Why?  Because  Spec  does not state a good
     \* * thing that (eventually) has to happen.  In its current form,  Spec  only defines
     \* * what must never happen (  Spec  itself is a safety property!).  However, since we
     \* * ask TLC to check if something good eventually happens, it finds those behaviors
     \* * permitted by  Spec, where nothing good ever happens.
     \* * We have to amend  Spec  such that it, in addition to the safety part, also defines
     \* * the liveness property we the system to satisfy.  Mathematically, this means we have
     \* * to conjoin  Spec  with some suitable liveness property  F:  Spec /\ F
    \* * Naively, we might choose for  F  the (liveness) property
     \* *  <>terminated  /\ <>terminationDetected.
=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl