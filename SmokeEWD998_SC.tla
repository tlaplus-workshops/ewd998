------------------------------- MODULE SmokeEWD998_SC -------------------------------
EXTENDS Naturals, TLC, IOUtils, CSV, Sequences

\* Filename for the CSV file that appears also in the R script and is passed
\* to the nested TLC instances that are forked below.
CSVFile ==
    "SmokeEWD998_SC" \o ToString(JavaTime) \o ".csv"

\* Write column headers to CSV file at startup of TLC instance that "runs"
\* this script and forks the nested instances of TLC that simulate the spec
\* and collect the statistics.
ASSUME 
    CSVWrite("BugFlags#Violation", <<>>, CSVFile)
    \* CSVWrite("BugFlags#Trace#Generated#Distinct", <<>>, CSVFile)

\* Command to fork nested TLC instances that simulate the spec and collect the
\* statistics. TLCGet("config").install gives the path to the TLC jar also
\* running this script.
Cmd == LET absolutePathOfTLC == TLCGet("config").install
       IN <<"java", "-jar",
          absolutePathOfTLC, 
          "-noTE",
          "-simulate",
          "SmokeEWD998.tla">>

ASSUME \A i \in 1..10 : \A bf \in SUBSET (1..6):
    LET ret == IOEnvExec([BF |-> bf, Out |-> CSVFile], Cmd).exitValue
    IN /\  CASE ret =  0 -> PrintT(<<JavaTime, bf>>)
             [] ret = 10 -> PrintT(<<bf, "Assumption violation">>)
             [] ret = 12 -> PrintT(<<bf, "Safety violation">>)
             [] ret = 13 -> PrintT(<<bf, "Liveness violation">>)
             \* For all other error codes, print TLC's error message.
             [] OTHER    -> Print(<<bf, IOEnvExec([BF |-> bf, Out |-> CSVFile], Cmd),
                                    "Error">>, FALSE)
       /\  CSVWrite("%1$s#%2$s", <<bf, ret>>, CSVFile)
       
===============================================================================