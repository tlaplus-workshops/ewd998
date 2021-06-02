We want to prove the temporal property  Stable  , which is defined as:

  Stable == [](terminationDetected => []terminated)

For the moment, Apalache supports only invariant checking.
Nevertheless, we can check the property  Stable  with Apalache.
If we look carefully at the temporal formula Stable, we can see that
it is sufficient to check the following:

1. Init => StableInv
2. StableInv /\ Next => StableInv'
3. StableInv /\ Next => StableActionInv

We can check that by issuing the following three queries:

$ apalache-mc check --config=APAsyncTerminationDetection.cfg --length=1 \
   --inv=StableInv --init=Init AsyncTerminationDetection_apalache.tla
$ apalache-mc check --config=APAsyncTerminationDetection.cfg --length=2 \
   --init=StableInv --inv=StableInv AsyncTerminationDetection_apalache.tla
$ apalache-mc check --config=APAsyncTerminationDetection.cfg --length=2 \
   --init=StableInv --inv=StableActionInv AsyncTerminationDetection_apalache.tla

We issue query 1 for a computation of length 1 (predicate Init is counted as a
step), whereas we issue queries 2-3 for computations of length 2 (StableInv, 
then Next).

---------------------- MODULE AsyncTerminationDetection_apalache ---------------------
EXTENDS AsyncTerminationDetection

\* This is a state invariant.
StableInv ==
    /\ TypeOK
    /\ (terminationDetected => terminated)

\* This is an action invariant.
StableActionInv ==    
    terminated => terminated'
======================================================================================
