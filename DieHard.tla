----------------------------- MODULE DieHard -----------------------------
EXTENDS Naturals

CONSTANTS SmallJugCapacity, BigJugCapacity, Target

ASSUME SmallJugCapacity \in (2..3) /\ BigJugCapacity \in (4..6) /\ Target = 4

VARIABLES smallJug, bigJug

Jugs == [smallJug: 0..SmallJugCapacity, bigJug: 0..BigJugCapacity]

Init == smallJug = 0 /\ bigJug = 0

FillSmallJug == smallJug' = SmallJugCapacity /\ bigJug' = bigJug

FillBigJug == smallJug' = smallJug /\ bigJug' = BigJugCapacity

EmptySmallJug == smallJug' = 0 /\ bigJug' = bigJug

EmptyBigJug == smallJug' = smallJug /\ bigJug' = 0

PourSmallToBig == IF smallJug + bigJug <= BigJugCapacity
                    THEN /\ smallJug' = 0
                         /\ bigJug' = bigJug + smallJug
                    ELSE /\ smallJug' = smallJug - (BigJugCapacity - bigJug)
                         /\ bigJug' = BigJugCapacity

PourBigToSmall == IF smallJug + bigJug <= SmallJugCapacity
                    THEN /\ smallJug' = smallJug + bigJug
                         /\ bigJug' = 0
                    ELSE /\ smallJug' = SmallJugCapacity
                         /\ bigJug' = bigJug - (SmallJugCapacity - smallJug)

Next == FillSmallJug \/ FillBigJug \/ EmptySmallJug \/ EmptyBigJug \/
         PourSmallToBig \/ PourBigToSmall

Invariant == bigJug <= BigJugCapacity /\ smallJug <= SmallJugCapacity

Spec == Init /\ [][Next]_<<smallJug, bigJug>> /\ WF_<<smallJug, bigJug>>(Next)

GoalReached == bigJug = Target \/ smallJug = Target

=============================================================================
