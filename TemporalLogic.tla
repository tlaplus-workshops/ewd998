--------------------------- MODULE TemporalLogic --------------------------------
EXTENDS Naturals, Sequences

F == FALSE
T == TRUE

VARIABLE p

seq ==
    {
        \* << F, T, 2 >>
        \* ,<< T, F, 2 >>
        \* ,<< T, 1 >>

        \* ,<< T, F, 1 >>
        \* ,<< F, T, T, T, F, 5 >>
        \* ,<< T, F, T, T, F, T, 6 >>
        \* ,<< F, T, T, T, F, 3 >>
    }

Prop ==
    /\ p = T
    \* /\   []p
    \* /\   <>p
    \* /\ <>[]p
    \* /\ []<>p

-------------------------------------------------------------------------------
\* Ignore the following!

VARIABLE c, b
vars == <<c, b, p>>

Init ==
    /\ b \in seq
    /\ c = 1
    /\ p = b[c] 

Next ==
    /\ UNCHANGED b
    /\ c' = IF c + 1 <= Len(b) - 1 THEN c + 1 ELSE b[Len(b)]
    /\ p' = b[c']

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

Alias ==
    \* Hide c and b variables.
    [ p |-> p ]

==============================================================================