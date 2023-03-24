0) Sending a message by node  i  increments a counter at  i  , the receipt of a message decrements i's counter
3) Receiving a *message* (not token) blackens the (receiver) node
2) An active node j -owning the token- keeps the token.  When j becomes inactive, it passes the token to its neighbor with  q = q + counter[j] 
4) A black node taints the token
7) Passing the token whitens the sender node
1) The initiator sends the token with a counter  q  initialized to  0  and color white
5) The initiator starts a new round iff the current round is inconclusive
6) The initiator whitens itself and the token when initiating a new round

https://github.com/tlaplus-workshops/ewd998/blob/032023/EWD998.tla

------- MODULE EWD998 -----

EXTENDS Naturals, Integers

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

Initator ==
    \* Who is the leader doesn't matter!
    CHOOSE n \in Node: TRUE

White == "white"
Black == "Black"
Colors == 
    {White,Black}

VARIABLE 
    active, 
    color,
    counter, 
    
    network,
    
    token \* [ q |-> 42, color |-> "white", pos |-> 0]
vars == <<active, network, color, counter, token>>

terminated ==
    \A n \in Node: active[n] = FALSE /\ network[n] = 0

terminationDetected ==
    /\ token.pos = 0
    /\ token.color = White
    /\ token.q + counter[0] = 0
    /\ ~active[0]
    /\ color[0] = White

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ color \in [ Node -> Colors ]
    /\ counter \in [ Node -> Int ]
    /\ network \in [ Node -> Nat ]
    /\ token \in [ q: Int, color: Colors, pos: Node]

Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ counter \in [ Node -> 0..0 ]
    /\ color \in [ Node -> Colors ]
    /\ network \in [ Node -> 0..0 ]
    /\ token \in [ q: {0}, color: {Black}, pos: Node]

InitiateToken ==
    \* ???
    /\ token.pos = 0
    /\ token' = [ token EXCEPT !["q"] = 0,
                               !["pos"]= N - 1,
                               !.color = White ]
    /\ color' = [ color EXCEPT ![token.pos] = White]                               
    /\ UNCHANGED <<counter, network, active>>

\* Foo==
\*     /\ token.pos = 0
\*     /\ UNCHANGED vars

PassToken ==
    /\ ~active[token.pos]
    /\ token.pos # 0
    /\ token' = [ token EXCEPT !["q"] = token.q + counter[token.pos],
                               !["pos"]= @ - 1,
                               !.color = IF color[token.pos] = Black
                                         THEN Black
                                         ELSE @ ]
    /\ color' = [ color EXCEPT ![token.pos] = White]                               
    /\ UNCHANGED <<counter, network, active>>

Terminates(n) ==
    \* /\ active[n] = TRUE \* ???
    /\ active' = [active EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<network, color, counter, token>>

SendMsg(snd, rcv) ==
    /\ UNCHANGED active
    /\ active[snd] = TRUE
    /\ network' = [ network EXCEPT ![rcv] = @ + 1 ]
    /\ counter' = [counter EXCEPT ![snd] = @ + 1]
    /\ UNCHANGED <<color, token>>

RecvMsg(rcv) ==
    /\ network[rcv] > 0
    \* /\ active[rcv] = TRUE \* ???
    /\ active' = [active EXCEPT ![rcv] = TRUE]
    /\ network' = [ network EXCEPT ![rcv] = network[rcv] - 1 ]
    /\ counter' = [counter EXCEPT ![rcv] = @ - 1]
    /\ UNCHANGED <<color, token>>

Next ==
    \E n,m \in Node:
        \/ Terminates(n)
        \/ SendMsg(n,m)
        \/ RecvMsg(n)
        \/ InitiateToken
        \/ PassToken

Spec ==
    Init /\ [] [Next]_vars /\ WF_vars(Next)

ATD ==
    INSTANCE AsyncTerminationDetection

ATDSpec == ATD!Spec

THEOREM Spec => ATDSpec

Alias ==
    [
        active |-> active, 
        color |-> color,
        counter |-> counter, 
        network |-> network,
        token |-> token,
        term |-> terminated,
        td |-> terminationDetected,

        IT |-> ENABLED InitiateToken,
        PT |-> ENABLED PassToken,
        NN |-> ENABLED Next
    ]

-------------------

Constraint ==
    \A n \in Node: network[n] < 3 /\ counter[n] \in -3..3

=====