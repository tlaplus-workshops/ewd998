------ MODULE MCAsyncTerminationDetection -----
EXTENDS AsyncTerminationDetection

MCInit ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> 0..3 ]
    /\ terminationDetected \in {FALSE, terminated}

Constraint ==
    \A n \in Node:
        pending[n] <= 3

ActionConstraint==
    \A n \in Node:
        pending[n] >= pending'[n]

=======