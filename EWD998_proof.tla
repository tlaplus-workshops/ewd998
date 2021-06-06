---------------------- MODULE EWD998_proof ---------------------
EXTENDS EWD998, TLAPS

USE NIsPosNat DEF 
        Color, Node, 
        Init, Spec, 
        Next, vars,
        System, InitiateProbe, PassToken, 
        Environment, SendMsg, RecvMsg, Deactivate, 
        TypeOK

LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK  OBVIOUS 
<1>2. TypeOK /\ [Next]_vars => TypeOK'
<1>3. QED BY <1>1, <1>2, PTL

THEOREM TerminationDetection == Spec => []IInv
<1> USE TypeCorrect DEF IInv, Inv, Sum
<1>1. Init => IInv
<1>2. IInv /\ [Next]_vars => IInv'   
<1>3. QED BY <1>1, <1>2, PTL

\* TODO Have fun and prove TerminationDetection above!  When done, file a PR
 \* TODO for the TLA+ examples at https://examples.tlapl.us  :-)

=============================================================================



\* The <1>1 proof obligation is not OBVIOUS, but the failed proof obligation
 \* nicely shows the equivalence of the special syntax for recursive functions  
 \*   F[e \in S] == ...  and  CHOOSE.
 \* Below is an excerpt of what TLAPS returns for <1>1:

ASSUME NEW CONSTANT N,
       NEW VARIABLE active,
       NEW VARIABLE pending,
       NEW VARIABLE color,
       NEW VARIABLE counter,
       NEW VARIABLE token,
       N \in Nat \ {0} 
PROVE  (/\ ...
       =>  ...
           /\ /\ P0::(B
                      = (CHOOSE sum :
                           sum
                           = [i \in 0..N - 1 |->
                                IF i = 0
                                  THEN counter[i]
                                  ELSE sum[i - 1] + counter[i]])[N - 1])
              /\ \/ P1:: ...
              