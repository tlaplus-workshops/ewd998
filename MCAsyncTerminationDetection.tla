----- MODULE MCAsyncTerminationDetection -----
EXTENDS AsyncTerminationDetection

MCInit ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> 0..3 ]
    /\ terminationDetected \in {FALSE, terminated}


Bound ==
    \A n \in Node: 
        pending[n] < 3

====