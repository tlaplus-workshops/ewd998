----- MODULE MCEWD998 -----
EXTENDS EWD998

StateConstraint ==
  /\ \A i \in Node : counter[i] < 3 /\ pending[i] < 3
  /\ token.counter < 3
=====