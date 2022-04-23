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

  token_pos |-> token_pos,
  token_tainted  |->  token_tainted,
  token_score |-> token_score,
  td |-> terminationDetected,
  t  |-> terminated


    ]

============