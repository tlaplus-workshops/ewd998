----- MODULE DieHard -----
EXTENDS Naturals

Min(a, b) == IF a < b THEN a ELSE b

VARIABLES big, small

Init ==
    /\ big = 0
    /\ small = 0

FillBig ==
    /\ big' = 5
    /\ UNCHANGED small

FillSmall ==
    /\ small' = 3
    /\ UNCHANGED big

EmptyBig ==
    /\ big' = 0
    /\ UNCHANGED small

EmptySmall ==
    /\ small' = 0
    /\ UNCHANGED big

Big2Small ==
    /\ big' = big - small
    /\ small' = Min(small + big, 3)
   
Small2Big ==
    /\ small' = small - big
    /\ big' = Min(small + big, 5)

Next ==
    \/ Big2Small
    \/ Small2Big
    \/ EmptyBig
    \/ EmptySmall
    \/ FillBig
    \/ FillSmall

Inv ==
    big # 4

=====