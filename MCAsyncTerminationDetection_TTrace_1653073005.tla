---- MODULE MCAsyncTerminationDetection_TTrace_1653073005 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, MCAsyncTerminationDetection

_expression ==
    LET MCAsyncTerminationDetection_TEExpression == INSTANCE MCAsyncTerminationDetection_TEExpression
    IN MCAsyncTerminationDetection_TEExpression!expression
----

_trace ==
    LET MCAsyncTerminationDetection_TETrace == INSTANCE MCAsyncTerminationDetection_TETrace
    IN MCAsyncTerminationDetection_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        pending = ((0 :> -1 @@ 1 :> 0 @@ 2 :> 0))
        /\
        active = ((0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE))
    )
----

_init ==
    /\ pending = _TETrace[1].pending
    /\ active = _TETrace[1].active
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ pending  = _TETrace[i].pending
        /\ pending' = _TETrace[j].pending
        /\ active  = _TETrace[i].active
        /\ active' = _TETrace[j].active

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("MCAsyncTerminationDetection_TTrace_1653073005.json", _TETrace)

=============================================================================

 Note that you can extract this module `MCAsyncTerminationDetection_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `MCAsyncTerminationDetection_TEExpression.tla` file takes precedence 
  over the module `BlockingQueue_TEExpression` below).

---- MODULE MCAsyncTerminationDetection_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, MCAsyncTerminationDetection

expression == 
    [
        \* To hide variables of the `MCAsyncTerminationDetection` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        pending |-> pending
        ,active |-> active
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_pendingUnchanged |-> pending = pending'
        
        \* Format the `pending` variable as Json value.
        \* ,_pendingJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(pending)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_pendingModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].pending # _TETrace[s-1].pending
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to deserialize the trace from a binary file.
 To create the file, replace your spec's invariant F with:
  Inv == IF F THEN TRUE ELSE ~IOSerialize(Trace, "file.bin", TRUE)
 (IOUtils module is from https://modules.tlapl.us/)
\*
\*---- MODULE MCAsyncTerminationDetection_TETrace ----
\*EXTENDS IOUtils, TLC, MCAsyncTerminationDetection
\*
\*trace == IODeserialize("file.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE MCAsyncTerminationDetection_TETrace ----
EXTENDS TLC, MCAsyncTerminationDetection

trace == 
    <<
    ([pending |-> (0 :> 0 @@ 1 :> 0 @@ 2 :> 0),active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE)]),
    ([pending |-> (0 :> 1 @@ 1 :> 0 @@ 2 :> 0),active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE)]),
    ([pending |-> (0 :> -1 @@ 1 :> 0 @@ 2 :> 0),active |-> (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE)])
    >>
----


=============================================================================

---- CONFIG MCAsyncTerminationDetection_TTrace_1653073005 ----
CONSTANTS
    N = 3

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Fri May 20 18:56:46 UTC 2022