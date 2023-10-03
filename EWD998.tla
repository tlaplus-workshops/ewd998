----- MODULE EWD998 -----

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
ASSUME NIsPosNat == N \in Nat \ {0}

Black == "b"
White == "w"

Color == {Black, White}

Initiator == 0

Nodes ==
    0 .. N-1

VARIABLE messages, active, color, counter, token

TypeOK ==
    /\ messages \in [ Nodes -> Nat ]
    /\ active \in [Nodes -> BOOLEAN ]
    /\ counter \in [Nodes -> Int ]
    /\ color \in [Nodes -> Color]
    /\ token \in [ pos: Nodes, color: Color, q: Int ]

termination ==
    \A n \in Nodes: active[n] = FALSE /\ messages[n] = 0

TerminationDetected ==
    /\ token.pos = 0
    /\ token.color = White
    /\ token.q + counter[0] = 0
    /\ active[0] = FALSE
    /\ color[0] = White

Init ==
    /\ messages = [ n \in Nodes |-> 0]
    /\ active = [ n \in Nodes |-> TRUE ]
    /\ color = [ n \in Nodes |-> White ]
    /\ counter = [ n \in Nodes |-> 0 ]
    /\ token = [ pos |-> 0, q |-> 0, color |-> Black ] \* ???? N-1

InitiateToken ==
    /\ token.pos = 0
    /\ token' = [ token EXCEPT !["pos"] = N - 1, !.q = 0, !.color = White]
    /\ color' = [color EXCEPT ![0] = White]
    /\ UNCHANGED <<active, counter, messages>>

PassToken ==
    /\ ~ active[token.pos]
    /\ token.pos # 0
    /\ color' = [ color EXCEPT ![token.pos] = White]
    /\ token' = [ token EXCEPT !.pos = @ - 1, 
                               !.color = IF color[token.pos] = Black THEN Black ELSE @, 
                               !.q = @ + counter[token.pos] ]
    /\ UNCHANGED <<active, counter, messages>>

Idle(node) ==
    \* /\ active' = [ n \in Nodes |-> IF n = node THEN FALSE ELSE active[n]]
    /\ active' = [ active EXCEPT ![node] = FALSE ]
    /\ UNCHANGED <<token, color, counter, messages>>

SendMsg(snd, rcv) ==
    /\ active[snd] = TRUE
    \* /\ messages' = [ n \in Nodes |-> IF n = rcv THEN messages[n] + 1 ELSE messages[n] ]
    \* /\ messages' = [ messages EXCEPT ![rcv] = messages[rcv] + 1 ]
    /\ messages' = [ messages EXCEPT ![rcv] = @ + 1 ]
    /\ counter' = [ counter EXCEPT ![snd] = @ + 1]
    /\ UNCHANGED <<active, color, token>>

RecvMsg(rcv) ==
    /\ messages[rcv] > 0
    /\ messages' = [ messages EXCEPT ![rcv] = @ - 1 ]
    /\ active' = [ active EXCEPT ![rcv] = TRUE ]
    \* eceiving a *message* (not token) blackens the (receiver) node
    /\ color' = [color EXCEPT ![rcv] = Black]
    \* /\ UNCHANGED color
    \* the receipt of a message decrements i's counter 
    /\ counter' = [ counter EXCEPT ![rcv] = @ - 1]
    /\ UNCHANGED token

Next ==
    \E n, m \in Nodes: 
        \/ Idle(n)
        \/ SendMsg(n,m)
        \/ RecvMsg(n)
        \/ PassToken
        \/ InitiateToken

----

OnlyThreeMsgs ==
    \A n \in Nodes: messages[n] < 4 /\ counter[n] \in -3..3


Inv ==
    TerminationDetected => termination

NeverTermination == 
    termination = FALSE

Good ==
    termination => <>TerminationDetected


Alias ==
    [
        active |-> active,
        color |-> color,
        counter |-> counter,
        messages |-> messages,
        token |-> token,
        TD |-> TerminationDetected,
        t |-> termination
    ]
\*****
=====
ATD => Inv
ATD => Goood

EWD998 => ATD

=====