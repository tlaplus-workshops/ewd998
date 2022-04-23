---- MODULE O ----

CONSTANT O(_)

\* THEOREM T1 ==     
\*     O(1) /\ O(2)    <=>   \E i \in {1,2}: O(i)      OBVIOUS


THEOREM T2 == 
    O(1) /\ O(2)    <=>    \A i \in {1,2}: O(i)     OBVIOUS



THEOREM T3 == O(1) \/ O(2) <=> \E i \in {1,2}: O(i) OBVIOUS



\* THEOREM T4 == O(1) \/ O(2) <=> \A i \in {1,2}: O(i) OBVIOUS
====
