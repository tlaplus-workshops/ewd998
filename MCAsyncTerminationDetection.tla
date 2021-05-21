---------------------- MODULE MCAsyncTerminationDetection ---------------------
EXTENDS AsyncTerminationDetection

StateConstraint ==
    \* * A (state-) constraint is a boolean-valued state function, i.e. a function
     \* * that is true or false of a state.
     \* * A state s, for which the constraint evaluates to FALSE, is not in the model.
     \* * TLC checks if s satisfies the properties (later!), but the successor states
     \* * of s are not generated.
     \* * Constraints are configured in TLC's configuration file
     \* * (MCAsyncTerminationDetection.cfg).
     \* * In this model, we restrict the state space to a finite fragment such that
     \* * at most three messages are pending.
    \A n \in Node : pending[n] <= 3

ActionConstraint ==
    \* * A state function cannot only be built from constant- and state-level operators.
     \* * Among others, the prime operator has action-level.  Thus, it cannot appear in
     \* * a state function such as this state constraint.  Fortunately, TLC also supports
     \* * action constraints.
     \* * There exists no node for which pending increases.
    ~ \E n \in Node: pending'[n] > pending[n]

\* * We could have stated the constraint in AsyncTerminationDetection.tla instead of
 \* * in a new module.  However, constraints are only relevant when model-checking
 \* * and not part of the system design.

\* Gradually increase the value of CONSTANT N in MCAsyncTerminationDetection.cfg
 \* and observe how quickly the size of the state space explodes (distinct states).
 \* Do we need a supercomputer for model-checking to be useful?  Usually, most bugs
 \* are found even with tiny models.  This is called the "small scope hyphothesis".
 \* If higher assurances are needed, one can write a proof for infinite domains with
 \* the TLA proof system. 
=============================================================================

| N | Diameter | Distinct States |
|---| ---|  --- |
| 4 | 17 |   4k | 
| 5 | 21 |  32k |
| 6 | 25 | 262k |
