
\* Cannot check  IInvA  as the invariant below because Apalache complains about  TypeOK  :
 \* Input error (see the manual): Found a set map over an infinite set of Int. Not supported.

\* Remove/comment  PROPERTY ATDSpec  in  MCEWD998.cfg  to stop Apalache (0.23.1) from complaining about:
 \*  AsyncTerminationDetection.tla:340:30-340:55: unsupported expression: WF_<<active, pending,...

$ apalache-mc check --inv=InvA --config=MCEWD998.cfg \
  --init=IInvA --next=Next --length=1 APEWD998

------------------------------ MODULE APEWD998 ------------------------------
EXTENDS Functions

CONSTANT
    \* @type: Int;
    N

VARIABLES 
    \* @type: Int -> Bool;
    active,
    \* @type: Int -> Int;
    pending,
    \* @type: Int -> Str;
    color,
    \* @type: Int -> Int;
    counter,
    \* @type: [pos: Int, q: Int, color: Str];
    token

INSTANCE EWD998

\* C  parameter of  SumA  because Apalache does not handle non-constant ranges
 \* (see https://git.io/JGFhg)
\* @type: (a -> b, Set(Int)) => b;
SumA(fun, C) ==
    LET \* @type: (Int, Int) => Int;
        Plus(a, b) == a + b
    IN FoldFunctionOnSet(Plus, 0, fun, C)

BA ==
    \* This spec counts the in-flight messages in the variable  pending  .
    SumA(pending, Node)

\* The set of nodes that have passed the token in this round.
 \* Previously written more concisely as  (token.pos+1)..N-1
 \* (see https://git.io/JGFhg)
Decided ==
    { n \in Node: n > token.pos }

\* The set of nodes that have not passed the token in this round yet.
 \* Previously written more concisely as  0..token.pos
 \* (see https://git.io/JGFhg)
Undecided ==
    { n \in Node: n <= token.pos }

InvA == 
    /\ P0:: BA = SumA(counter, Node)
    /\  \/ P1:: /\ \A i \in Decided : ~ active[i]
            /\ IF token.pos = N-1 
               THEN token.q = 0 
               ELSE token.q = SumA(counter, Decided)
        \/ P2:: SumA(counter, Undecided) + token.q > 0
        \/ P3:: \E i \in Undecided : color[i] = "black"
        \/ P4:: token.color = "black"

IInvA ==
    \* Conjoin  TypeOK  to define the types of the variables.  This is somewhat
     \* redundant given Apalache's type annotations.
    /\ TypeOK
    /\ InvA

=============================================================================
