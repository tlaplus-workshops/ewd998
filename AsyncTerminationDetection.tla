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
  pending               \* number of messages pending at a node

\* * A definition that lets us refer to the spec's variables (more on it later).
vars == << active, pending >>

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
    /\ active = [ n \in Node |-> TRUE ]
    /\ pending = [ n \in Node |-> 0 ]

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

\* * Node i sends a message to node j.
SendMsg(i, j) ==
    /\ active[i]
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED active

\* * Node I receives a message.
Wakeup(i) ==
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 2]

-----------------------------------------------------------------------------

\* * Here we define the complete next-state action. Recall that it’s a predicate
 \* * on two states — the current and the next — which is true if the next state
 \* * is acceptable.
 \* * The next-state relation should somehow plug concrete values into the 
 \* * (sub-) actions Terminate, SendMsg, and Wakeup.  For the moment, let's assume
 \* * N = 4 and plug the values in explicitly.
Next ==
        \* * A TLA+ specification is a formula and TLC evaluates it.  With the
         \* * conjunct list, ignoring the temporal logic for now, we essentially
         \* * stated the following formula 
         \* *   /\ active = [n \in Node |-> FALSE]
         \* *   /\ active[0] = TRUE
         \* *   /\ active[1] = TRUE
         \* *   /\ active[2] = TRUE
         \* *   /\ active[3] = TRUE
         \* * which is FALSE causing TLC to terminate after printing the initial state.
        \* TODO Can we rewrite this s.t. it takes the spec parameter CONSTANT N into account?
         \* TODO Create a new file O.tla with the following content:
         \* TODO   ---- MODULE O ----
         \* TODO   CONSTANT O(_)
         \* TODO   THEOREM O(1) /\ O(2) <=> \E i \in {1,2}: O(i) OBVIOUS
         \* TODO   THEOREM O(1) /\ O(2) <=> \A i \in {1,2}: O(i) OBVIOUS
         \* TODO   THEOREM O(1) \/ O(2) <=> \E i \in {1,2}: O(i) OBVIOUS
         \* TODO   THEOREM O(1) \/ O(2) <=> \A i \in {1,2}: O(i) OBVIOUS
         \* TODO   ====
         \* TODO Switch to the terminal and check what the TLA+ proof system, which one
         \* TODO are valid THEOREMs: `tlapm O.tla`:
        \/ Terminate(0)
        \/ Terminate(1)
        \/ Terminate(2)
        \/ Terminate(3)
        \/ Wakeup(0)
        \/ Wakeup(1)
        \* Rest omitted.

=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by Stephan Merz @muenchnerkindl