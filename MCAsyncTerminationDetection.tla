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
     \* * In this model we restrict the state space to a finite fragment such that
     \* * at most three messages are pending.
    \* TODO Restrict the model to those states where pending is less than four for all
     \* TODO Nodes of the system.
    TRUE

\* * We could have stated the constraint in AsyncTerminationDetection.tla instead of
 \* * in a new module.  However, constraints are only relevant when model-checking
 \* * and not part of the system design.

\* TODO Gradually increase the value of CONSTANT N in MCAsyncTerminationDetection.cfg
 \* TODO and observe how quickly the size of the state space explodes (distinct states).
 \* TODO Do we need a supercomputer for model-checking to be useful?  Usually, most bugs
 \* TODO are found even with tiny models.  This is called the "small scope hyphothesis".
 \* TODO If higher assurances are needed, one can write a proof for infinite domains with
 \* TODO the TLA proof system. 
=============================================================================
