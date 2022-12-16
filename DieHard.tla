----- MODULE DieHard -------
EXTENDS Naturals

Max(a, b) == IF a > b THEN a ELSE b
Min(a, b) == IF a < b THEN a ELSE b

VARIABLE big, small

TypeOK ==
    /\ big \in 0..5
    /\ small \in 0..3    
    
Init == big = 0 /\ small = 0

FillBig == big' = 5 /\ small' = small

FillSmall == big' = big /\ small' = 3

EmptyBig == big' = 0 /\ small' = small

EmptySmall == small' = 0 /\ big' = big

Big2Small == 
    /\ big' = Max(0, big - (3 - small))
    /\ small' = Min(3, small + big)

Small2Big ==
    /\ big' = Min(5, big + small)
    /\ small' = Max(0, small - (5 - big))

Next ==
    \/ EmptyBig \/ EmptySmall
    \/ FillBig \/ FillSmall
    \/ Big2Small \/ Small2Big

DefuseBomb ==
    big # 4

======
