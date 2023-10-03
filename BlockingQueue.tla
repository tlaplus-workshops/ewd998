----- MODULE BlockingQueue -----
EXTENDS Naturals, FiniteSets    

CONSTANT bufCap, P, C

ASSUME /\ bufCap \in Nat
       /\ IsFiniteSet(P)
       /\ P # {}
       /\ IsFiniteSet(C)
       /\ C # {}

VARIABLE buf, waitSet
vars == <<buf, waitSet>>

TypeOK ==
    /\ buf \in 0..bufCap
    /\ waitSet \in SUBSET (P \union C)

Init ==
    /\ buf = 0
    /\ waitSet = {}

Notify ==
    IF waitSet = {} THEN UNCHANGED waitSet
    ELSE \E t \in waitSet: waitSet' = waitSet \ {t}

NotifyAll ==
    waitSet' = {}

NotifyOther(T) ==
    IF waitSet \cap T = {} THEN UNCHANGED waitSet
    ELSE \E t \in waitSet \cap T : waitSet' = waitSet \ {t}

Wait(self) ==
    waitSet' = waitSet \union {self}

Put(self) ==
    \/ /\ bufCap > buf
       /\ buf' = buf + 1
       /\ Notify
    \/ /\ bufCap = buf
       /\ Wait(self)
       /\ UNCHANGED buf

Get(self) ==
    \/ /\ buf > 0
       /\ buf' = buf - 1
       /\ Notify
    \/ /\ buf = 0
       /\ Wait(self)
       /\ UNCHANGED buf

Next ==
    \E t \in (P \union C) \ waitSet:
        \/ /\ t \in P
           /\ Put(t)
        \/ /\ t \in C
           /\ Get(t)

BQSpec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

DeadlockFree ==
    [](waitSet # P \union C)

Foo ==
    <>(buf = bufCap)

\* BQ => DeadlockFree
\* BQS => DeadlockFree
\* BQS => BQ

\* <>[]P
\* []<>P

StarvationFreedom ==
    /\ \A p \in P: []<> <<Put(p)>>_<<buf,waitSet>>
    /\ \A c \in C: []<> <<Get(c)>>_<<buf,waitSet>>

====