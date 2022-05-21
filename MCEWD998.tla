-----  MODULE MCEWD998 -----

EXTENDS EWD998

\* MCInit == 
\*     /\ pending \in [Node -> 0..3]
\*     /\ ...

Bound ==
    \A n \in Node: pending[n] < 3 /\ counter[n] \in -2..2

=========