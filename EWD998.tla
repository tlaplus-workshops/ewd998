---------------------- MODULE EWD998 ---------------------
EXTENDS Integers

Range(f) ==
    { f[x] : x \in DOMAIN f }

CONSTANT N

ASSUME NIsPosNat == N \in Nat \ {0}

Node == 0 .. N-1

Color == {"white", "black"}

VARIABLES 
  active,               \* activation status of nodes
  tainted,
  score,
  
  \* Network:
  pending,               \* number of messages pending at a node

    token
\*   token_pos,
\*   token_tainted,
\*   token_score

\* * A definition that lets us refer to the spec's variables (more on it later).
vars == << active, pending, score, tainted, token >>

terminated ==
    \A n \in Node: active[n] = FALSE /\ pending[n] = 0

terminationDetected ==
    /\ token.pos = 0
    /\ token.score + score[0] = 0
    /\ token.tainted = "white"
    /\ tainted[0] = "white"
    /\ active[0] = FALSE

-----------------------------------------------------------------------------

\* * Initially, all nodes are active and no messages are pending.
Init ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ score = [n \in Node |-> 0]
    /\ tainted = [n \in Node |-> "white"]

    /\ pending = [ n \in Node |-> 0 ]

    /\ token = [ pos |-> 0, tainted |-> "black", score |-> 0]

TypeOK ==
    /\ active \in [ Node -> BOOLEAN ]
    /\ pending \in [ Node -> Nat ]
    /\ token \in [ pos: Node, tainted: Color, score: Int ]
    /\ score \in [Node -> Int]
    /\ tainted \in [Node -> Color]
    
-----------------------------------------------------------------------------
TokenPass ==
    /\ token.pos # 0
    /\ active[token.pos] = FALSE
    
    /\ token' = [ pos |-> token.pos - 1, 
                  tainted |-> IF tainted[token.pos] = "white" THEN token.tainted ELSE "black", 
                  score |-> token.score + score[token.pos] ]

    /\ tainted' = [ tainted EXCEPT ![token.pos] = "white"]
    /\ UNCHANGED <<score, active, pending>> 

InitiateToken ==
    /\ ~terminationDetected
    /\ active[0] = FALSE
    /\ token.pos = 0
    /\ token' = [ pos |-> N-1, 
                  tainted |-> "white", 
                  score |-> 0 ]
    /\ tainted' = [ tainted EXCEPT ![0] = "white"]
    /\ UNCHANGED <<score, active, pending>>

-------------------------------------------------------

Terminate(i) ==
    \* /\ active[i] = TRUE
    /\ active' = [ active EXCEPT ![i] = FALSE ]
    /\ pending' = pending
    /\ UNCHANGED <<tainted, score>>
    /\ UNCHANGED <<token>>

\* * Node i sends a message to node j.
SendMsg(i,j) ==
    \* /\ i # j
    /\ active[i]
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ score' = [score EXCEPT ![i] = @ + 1]
    /\ UNCHANGED <<active, tainted, token>>

\* * Node I receives a message.
Wakeup(i) ==
    \* /\ active[i] = FALSE
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ score' = [score EXCEPT ![i] = @ - 1]
    /\ tainted' = [tainted EXCEPT ![i] = "black"]
    /\ UNCHANGED <<token>>

Next ==
    \/ InitiateToken
    \/ TokenPass
    \/ \E i,j \in Node:
        \/ Terminate(i)
        \/ Wakeup(i)
        \/ SendMsg(i,j)

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)


-------------------------------------------

ATD == INSTANCE AsyncTerminationDetection

ATDSpec == ATD!Spec
THEOREM Implements == Spec => ATDSpec

\* Usually, one would find additional invariants and liveness properties at this
 \* stage and check the spec for different spec parameters.  The second part can
 \* easily be parallelized and scaled out (hello cloud computing!).
\* If higher assurances are needed, now would be the start of proving  EWD998
 \* correct, which requires finding an inductive invariant.  Finding an
 \* inductive invariant is hard because one has to know *why* the algorithm
 \* works (model-checking only confirms that algorithms work according to the
 \* checked properties).
\* Fortunately, the EWD998 paper gives an inductive invariant in the form of a
 \* larger formula  P0 /\ (P1 \/ P2 \/ P3 \/ P4)  , with  \S  representing
 \* "the sum of",  B  to equal the sum of in-flight messages,  and  P0  to  P4 : 
 \*
 \* P0: B = Si: 0 <= i < N: c.i)
 \* P1: (Ai: t < i < N: machine nr.i is passive) /\
 \*     (Si: t < i < N: c.i) = q
 \* P2: (Si: 0 <= i <= t: c.i) + q > 0
 \* P3: Ei: 0 <= i <= t : machine nr.i is black
 \* P4: The token is black

\* f \in [ Node -> Int], from \in Node, to \in Node, from <= to
SumOf2(f, from, to) ==
    LET sum[i \in from..to] == IF i = from THEN f[from] ELSE sum[i - 1] + f[i]
    IN IF from > to THEN 0 ELSE sum[to]

RECURSIVE SumOf3(_,_,_)
SumOf3(f, from, to) ==
    IF from > to THEN 0 ELSE 
        IF from = to THEN f[from]
        ELSE f[from] + SumOf3(f, from + 1, to)

RECURSIVE SumOf(_,_)
SumOf(f, S) ==
    IF S = {} THEN 0
    ELSE LET i == CHOOSE n \in S: TRUE
         IN f[i] + SumOf(f, S \ {i})

SumOfFold(f, from , to) ==
    LET F == INSTANCE Functions IN F!FoldFunctionOnSet(+, 0, f, from..to)

\*RECURSIVE otherSum()
\*  return a[0] + otherSum(a[1-N])

B ==
    SumOf(pending, 0..N-1)

Inv ==
    [](
    /\ P0:: B = SumOf(score, 0..N-1)
    /\ \/ P1:: /\ \A i \in token.pos+1..N-1: active[i] = FALSE
               /\ SumOf(score, token.pos+1..N-1) = token.score
       \/ P2:: SumOf(score, 0..token.pos) + token.score > 0
       \/ P3:: \E n \in 0..token.pos: tainted[n] = "black"
       \/ P4:: token.tainted = "black")

=============================================================================
Safe ==
    terminationDetected => terminated

Live ==
    [](terminated => <>terminationDetected)

