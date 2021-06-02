------------------------------- MODULE SmokeEWD998 -------------------------------
EXTENDS MCEWD998, TLC

\* SmokeInit is configured to re-define the initial predicate. We use  SmokeInit
\* to randomly select a subset of the defined initial states in cases when the
\* set of all initial states is too expensive to generate during smoke testing.
SmokeInit ==
    /\ pending = [i \in Node |-> 0]
    /\ counter = [i \in Node |-> 0]
    /\ active = [n \in Node |-> RandomElement(BOOLEAN)]
    /\ color = [n \in Node |-> RandomElement(Color)]
    /\ token = [pos |-> 0, q |-> 0, color |-> "black"]

\* StopAfter  has to be configured as a state constraint. It stops TLC after ~1
\* second or after generating 100 traces, whatever comes first, unless TLC
\* encountered an error.  In this case,  StopAfter  has no relevance.
StopAfter ==
    TLCGet("config").mode = "simulate" =>
    (* The smoke test has a time budget of 1 second. *)
    \/ TLCSet("exit", TLCGet("duration") > 1)
    (* Generating 100 traces should provide reasonable coverage. *)
    \/ TLCSet("exit", TLCGet("diameter") > 100)

===============================================================================