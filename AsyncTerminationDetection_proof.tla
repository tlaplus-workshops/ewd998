---------------------- MODULE AsyncTerminationDetection_proof ---------------------
EXTENDS AsyncTerminationDetection, TLAPS

(* Do not whitelist all the known facts/assumptions and definitions to speedup provers *)
\*USE NIsPosNat DEF vars, terminated, Node,
\*                  Init, Next, Spec,
\*                  DetectTermination, Terminate,
\*                  Wakeup, SendMsg,
\*                  TypeOK, Stable

\* * An invariant I is inductive, iff Init => I and I /\ [Next]_vars => I. Note
\* * though, that TypeOK itself won't imply  Stable  though!  TypeOK alone
\* * does not help us prove Stable.

LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK BY NIsPosNat DEF Init, TypeOK, Node, terminated
<1>2. TypeOK /\ [Next]_vars => TypeOK'
 <2> SUFFICES ASSUME TypeOK,
                     [Next]_vars
              PROVE  TypeOK'
   OBVIOUS
 <2>1. CASE DetectTermination
   BY <2>1 DEF TypeOK, Next, vars, DetectTermination
 <2>2. ASSUME NEW i \in Node,
              NEW j \in Node,
              Terminate(i)
       PROVE  TypeOK'
   BY <2>2 DEF TypeOK, Next, vars, Terminate, terminated
 <2>3. ASSUME NEW i \in Node,
              NEW j \in Node,
              Wakeup(i)
       PROVE  TypeOK'
   BY <2>3 DEF TypeOK, Next, vars, Wakeup
 <2>4. ASSUME NEW i \in Node,
              NEW j \in Node,
              SendMsg(i, j)
       PROVE  TypeOK'
   BY <2>4 DEF TypeOK, Next, vars, SendMsg
 <2>5. CASE UNCHANGED vars
   BY <2>5 DEF TypeOK, Next, vars
 <2>6. QED
   BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED BY <1>1, <1>2, PTL DEF Spec

\* ? How do we prove   Spec => Stable  ?
 \* ? We would have to find an inductive invariant  IInv  that implies  Stable  ,
 \* ? (unless  Stable  happens to be inductive).  Usually, we start with  TypeOK
 \* ? and conjoin additional constraints.  The proof then is as follows:
IInv ==
    /\ TypeOK
    /\ TRUE \* The additional constraints here.

THEOREM Termination == Spec => Stable
<1>1. Init => IInv
<1>2. IInv /\ [Next]_vars => IInv'
<1>3. IInv => Stable
<1>. QED BY <1>1, <1>2, <1>3 DEF Spec, Stable

=============================================================================
