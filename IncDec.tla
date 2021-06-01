Apalache is the new kid on the block.  Where TLC
implements finite-state model-checking, Apalache
implements bounded model-checking.  Apalache
underpins a powerful SMT solver that can answer
queries such as  \E n \in 1..Nat : n \in Nat
without enumerating the values of  n  (TLC won't
even try to enumerate  Nat).

Let's see the different powers of Apalache and
TLC...

### Run tools

$ apalache-mc check --inv=Inv --length=10 \
  IncDec.tla

$ tlc -config IncDec.tla IncDec.tla

### Quick demo

1) Check spec as is
2) Increment --length to 11
3) Increment  Inv  and  --length  to 1000
4) Change  Init  to  v \in Nat
4a) Go Apalache!
    (But no longer useful counter-examples
     when checking inductive invariants)
4b) TLC gives up
    (Workaround: Randomization.tla with 
    RandomSubset(42,0..10000000))

---- MODULE IncDec ----
EXTENDS Integers, Randomization

VARIABLE
    \* @type: Int;
    v

Init ==
    /\ v = 0

Inc ==
    /\ v >= 0
    /\ v' = v + 1

Dec ==
    /\ v <= 0
    /\ v' = v - 1

Next ==
    \/ Inc
    \/ Dec

Inv ==
    /\ v <  10
    /\ v > -10

====
---- CONFIG IncDec ----
INIT Init
NEXT Next
INVARIANT Inv
====