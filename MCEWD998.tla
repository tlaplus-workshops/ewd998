------ MODULE MCEWD998 ------
EXTENDS EWD998

Constraint ==
    \A n \in Node:
        /\ pending[n] \in 0..3
        /\ score[n] \in -3..3

Alias ==
    
    [
        active |-> active,
        tainted |-> tainted,
    score |-> score,
    pending |-> pending,               \* number of messages pending at a node

  token |-> token,
  td |-> terminationDetected,
  t  |-> terminated


    ]

============