------------------------------- MODULE MCEWD998 -------------------------------
EXTENDS EWD998, TLC

(***************************************************************************)
(* Bound the otherwise infinite state space that TLC has to check.         *)
(***************************************************************************)
StateConstraint ==
  /\ \A i \in Node : counter[i] < 3 /\ pending[i] < 3
  /\ token.q < 3

-----------------------------------------------------------------------------

\* Note that the non-property  TLCGet("level") < 42  combined with TLC's
 \* simulator quickly triggers som "counter-example" for MCEWD998.
MaxDiameter == TLCGet("level") < 42

\* $ tlc -noTE -simulate -deadlock MCEWD998 | grep -A1 "sim = TRUE"
Alias ==
    [
        active |-> active
        ,color |-> color
        ,counter |-> counter
        ,pending |-> pending
        ,token |-> token
        
        \* Eye-ball test if some nodes simultaneously deactivate. Note that
         \* the nodes deactive in the *successor* (primed) state.
        ,sim |-> \E i,j \in Node:
                        /\ i # j
                        /\ active[i] # active[i]'
                        /\ active[j] # active[j]'
        \* Yes, one can prime  TLCGet("...")  in recent version of TLC! With it,
         \* we account for the  sim  being true when the nodes deactivate in the
         \* successor state.  Obviously, .name will be "Deactivate".
        ,action |-> TLCGet("action")'.name
    ]

-----------------------------------------------------------------------------

\* With TLC, checking  IInv /\ [Next]_vars => IInv'  translate to a config s.t.
 \*
 \*  CONSTANT N = 3
 \*  INIT IInv
 \*  NEXT Next
 \*  INVARIANT IInv
 \*
 \* However, the number of states defined by  TypeOK  is infinite because of 
 \* sub-formulas involving undound sets (Nat & Int).  Therefore, we rewrite
 \*  TypeOk  and substitute  MyNat  for Nat  and  MyInt  for  Int  ,
 \* respectively.
 \* Alternatively, we could have re-defined  Nat  with  MyNat  and  Int  with
 \*  MyInt  . 
\* TODO Do you see why re-defining  Nat  and  Int  would have caused problems?

MyNat == 0..3
MyInt == -2..2

IInit ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> MyNat]
    /\ color \in [Node -> Color]
    /\ counter \in [Node -> MyInt]
    /\ token \in [ pos: Node, q: MyInt, color: Color ]
    /\ Inv

=============================================================================

$ tlc -deadlock -config MCEWD998.tla MCEWD998

------------------------------ CONFIG MCEWD998 ------------------------------

CONSTANT N = 3

INIT IInit
NEXT Next

INVARIANT IInv

CONSTRAINT StateConstraint

=============================================================================

TLC2 Version 2.16 of Day Month 20?? (rev: 5682c4a)
Running breadth-first search Model-Checking with fp 75 and seed 6362907857480250600 with 1 worker on 4 cores with 5291MB heap and 64MB offheap memory [pid: 245607] (Linux 5.4.0-74-generic amd64, Ubuntu 11.0.11 x86_64, MSBDiskFPSet, DiskStateQueue).
Parsing file /home/markus/src/TLA/ewd998/MCEWD998.tla
Parsing file /home/markus/src/TLA/ewd998/EWD998.tla
Parsing file /tmp/Integers.tla (jar:file:/opt/toolbox/tla2tools.jar!/tla2sany/StandardModules/Integers.tla)
Parsing file /tmp/Naturals.tla (jar:file:/opt/toolbox/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)
Parsing file /home/markus/src/TLA/ewd998/AsyncTerminationDetection.tla
Semantic processing of module Naturals
Semantic processing of module Integers
Semantic processing of module AsyncTerminationDetection
Semantic processing of module EWD998
Semantic processing of module MCEWD998
Starting... (2021-06-05 18:13:27)
Computing initial states...
Computed 2 initial states...
Computed 4 initial states...
Computed 8 initial states...
Computed 16 initial states...
Computed 32 initial states...
Computed 64 initial states...
Computed 128 initial states...
Computed 256 initial states...
Computed 512 initial states...
Computed 1024 initial states...
Computed 2048 initial states...
Computed 4096 initial states...
Computed 8192 initial states...
Computed 16384 initial states...
Computed 32768 initial states...
Computed 65536 initial states...
Computed 131072 initial states...
Computed 262144 initial states...
Computed 524288 initial states...
Finished computing initial states: 696928 states generated, with 507184 of them distinct at 2021-06-05 18:14:47.
Progress(2) at 2021-06-05 18:14:50: 850,004 states generated (850,004 s/min), 509,765 distinct states found (509,765 ds/min), 454,600 states left on queue.
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.4E-7
  based on the actual fingerprints:  val = 1.4E-10
4895579 states generated, 599598 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 36.
The average outdegree of the complete state graph is 0 (minimum is 0, the maximum 7 and the 95th percentile is 1).
Finished in 01min 54s at (2021-06-05 18:15:20)
