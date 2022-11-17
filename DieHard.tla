------- MODULE DieHard --------
EXTENDS Naturals

Min(m,n) == IF m < n THEN m ELSE n

VARIABLES small, big

FillSmall ==
    /\ small' = 3
    /\ UNCHANGED big
    
FillBig == 
    /\ big' = 5
    /\ UNCHANGED small
    
SmallToBig ==
    /\ big' = Min(5, big + small)
    /\ small' = small - (big' - big)
    
BigToSmall ==
    /\ small' =  Min (3, big + small)
    /\ big' = big - (small' - small) 
    
EmptySmall ==
    /\ small' = 0
    /\ UNCHANGED big

EmptyBig ==
    /\ big' = 0
    /\ UNCHANGED small

Init ==
    /\ big = 0 
    /\ small = 0
    
Next ==
    \/ FillSmall
    \/ FillBig    
    \/ EmptySmall
    \/ EmptyBig
    \/ SmallToBig
    \/ BigToSmall    
    
Inv ==
    big # 4

TypeOK ==
    big \in 0..5 /\ small \in 0..3

====