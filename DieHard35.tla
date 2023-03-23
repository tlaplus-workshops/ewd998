------------------------ MODULE DieHard35 ------------------------
EXTENDS Naturals

CONSTANTS big_jug, small_jug, goal
VARIABLES b_amount, s_amount

Init == (b_amount = 0) /\ (s_amount = 0)

FillBig == b_amount' = big_jug /\ s_amount' = s_amount

FillSmall == s_amount' = small_jug /\ b_amount' = b_amount

EmptyBig == b_amount' = 0 /\ s_amount' = s_amount

EmptySmall == s_amount' = 0 /\ b_amount' = b_amount

PourBigToSmall == 
    LET amount = min(b_amount, small_jug - s_amount)
    IN s_amount' = s_amount + amount /\ b_amount' = b_amount - amount

PourSmallToBig == 
    LET amount = min(s_amount, big_jug - b_amount)
    IN b_amount' = b_amount + amount /\ s_amount' = s_amount - amount

Goal == (b_amount = goal) \/ (s_amount = goal)

Next == 
    FillBig \/ FillSmall \/ EmptyBig \/ EmptySmall \/ PourBigToSmall \/ PourSmallToBig

DieHard == Init /\ [][Next]_<<b_amount, s_amount>>

==================================================================
