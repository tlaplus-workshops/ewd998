---------------------- MODULE AsyncTerminationDetection_proof ---------------------
EXTENDS AsyncTerminationDetection, TLAPS

(* Whitelist all the known facts/assumptions and definitions *)
USE NIsPosNat DEF vars, terminated, Node,
                  Init, Next, Spec,
                  DetectTermination, Terminate,
                  Wakeup, SendMsg,
                  TypeOK, Stable

\* * An invariant I is inductive, iff Init => I and I /\ [Next]_vars => I. Note
\* * though, that TypeOK itself won't imply  Stable  though!  TypeOK alone
\* * does not help us prove Stable.

\* TODO Prove  TypeOK  inductive.
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK BY NIsPosNat DEF Init, TypeOK, Node, terminated
<1>2. TypeOK /\ [Next]_vars => TypeOK'  OBVIOUS 
<1>. QED BY <1>1, <1>2, PTL

=============================================================================
