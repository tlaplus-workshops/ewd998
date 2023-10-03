----- MODULE BlockingQueueSplit ------
EXTENDS Naturals, FiniteSets    

CONSTANT bufCap, P, C

ASSUME /\ bufCap \in Nat
       /\ IsFiniteSet(P)
       /\ P # {}
       /\ IsFiniteSet(C)
       /\ C # {}

VARIABLE buf, waitSetC, waitSetP
vars ==<<buf, waitSetC, waitSetP>>

TypeOK ==
    /\ buf \in 0..bufCap
    /\ waitSetC \in SUBSET (C)
    /\ waitSetP \in SUBSET (P)

Init ==
    /\ buf = 0
    /\ waitSetC = {}
    /\ waitSetP = {}

Notify(ws) ==
    IF ws = {} THEN UNCHANGED ws
    ELSE \E t \in ws: ws' = ws \ {t}

Wait(ws, self) ==
    ws' = ws \union {self}

Put(self) ==
    \/ /\ bufCap > buf
       /\ buf' = buf + 1
       /\ Notify(waitSetC)
       /\ UNCHANGED waitSetP
    \/ /\ bufCap = buf
       /\ Wait(waitSetP, self)
       /\ UNCHANGED <<buf, waitSetC>>

Get(self) ==
    \/ /\ buf > 0
       /\ buf' = buf - 1
       /\ Notify(waitSetP)
       /\ UNCHANGED waitSetC
    \/ /\ buf = 0
       /\ Wait(waitSetC, self)
       /\ UNCHANGED <<buf, waitSetP>>

Next ==
    \E t \in (P \union C) \ (waitSetC \union waitSetP):
        \/ /\ t \in P
           /\ Put(t)
        \/ /\ t \in C
           /\ Get(t)

BQSSpec ==
    Init /\ [][Next]_vars

\* BQS => BQ

BQ ==
    INSTANCE BlockingQueue WITH waitSet <- waitSetP \union waitSetC

BQSpec ==
    BQ!BQSpec

THEOREM Implements == BQSSpec => BQSpec
THEOREM Types == BQSSpec => TypeOK
=====