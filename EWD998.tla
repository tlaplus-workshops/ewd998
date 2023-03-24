0) Sending a message by node  i  increments a counter at  i  , the receipt of a
   message decrements i's counter
3) Receiving a *message* (not token) blackens the (receiver) node
2) An active node j -owning the token- keeps the token.  When j becomes inactive,
   it passes the token to its neighbor with  q = q + counter[j] 
4) A black node taints the token
7) Passing the token whitens the sender node
1) The initiator sends the token with a counter  q  initialized to  0  and color
   white
5) The initiator starts a new round iff the current round is inconclusive
6) The initiator whitens itself and the token when initiating a new round


------- MODULE EWD998 -----

EXTENDS Naturals

\* * A constant is a parameter of a specification. In other words, it is a
 \* * "variable" that cannot change throughout a behavior, i.e., a sequence
 \* * of states. Below, we declares N to be a constant of this spec.
 \* * We don't know what value N has or even what its type is; TLA+ is untyped and
 \* * everything is a set. In fact, even 23 and "frob" are sets and 23="frob" is 
 \* * syntactically correct.  However, we don't know what elements are in the sets 
 \* * 23 and "frob" (nor do we care). The value of 23="frob" is undefined, and TLA+
 \* * users call this a "silly expression".
CONSTANT N 

\* * We should declare what we assume about the parameters of a spec--the constants.
 \* * In this spec, we assume constant N to be a (positive) natural number, by
 \* * stating that N is in the set of Nat (defined in Naturals.tla) without 0 (zero).
 \* * Note that the TLC model-checker, which we will meet later, checks assumptions
 \* * upon startup.
NIsPosNat == N \in Nat \ {0}

ASSUME NIsPosNat

Node == 0 .. N - 1 

VARIABLE active, network
vars == <<active, network>>

terminated ==
    \A n \in Node: active[n] = FALSE /\ network[n] = 0

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> Nat ]

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ network \in [ Node -> 0..3 ]

Terminates(n) ==
    \* /\ active[n] = TRUE
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<network>>

SendMsg(snd, rcv) ==
    /\ UNCHANGED active
    /\ active[snd] = TRUE
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]

RecvMsg(rcv) ==
    /\ network[rcv] > 0
    \* /\ active[rcv] = TRUE \* ???
    /\ active' = [active EXCEPT ![rcv] = TRUE]
    /\ network' = [ network EXCEPT ![rcv] = network[rcv] - 1 ]

Next ==
    \E n,m \in Node:
        \/ Terminates(n)
        \/ SendMsg(n,m)
        \/ RecvMsg(n)

Spec ==
    Init /\ [] [Next]_vars /\ WF_vars(Next)

-------------------

Constraint ==
    \A n \in Node: network[n] < 3

=====