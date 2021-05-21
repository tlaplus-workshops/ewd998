---- MODULE F ----
EXTENDS Naturals, FiniteSets

(* 1. Set of all permutations of {"T","L","A"} including repetitions. *)
PermsWithReps(S) ==
    "Finish exercise 1."
    
ASSUME 
    PermsWithReps({"T","L","A"}) =
        {<<"T", "T", "T">>, <<"T", "T", "L">>, <<"T", "T", "A">>, 
            <<"T", "L", "T">>, <<"T", "L", "L">>, <<"T", "L", "A">>, 
            <<"T", "A", "T">>, <<"T", "A", "L">>, <<"T", "A", "A">>, 
            <<"L", "T", "T">>, <<"L", "T", "L">>, <<"L", "T", "A">>, 
            <<"L", "L", "T">>, <<"L", "L", "L">>, <<"L", "L", "A">>, 
            <<"L", "A", "T">>, <<"L", "A", "L">>, <<"L", "A", "A">>, 
            <<"A", "T", "T">>, <<"A", "T", "L">>, <<"A", "T", "A">>, 
            <<"A", "L", "T">>, <<"A", "L", "L">>, <<"A", "L", "A">>, 
            <<"A", "A", "T">>, <<"A", "A", "L">>, <<"A", "A", "A">>}

(* 2. All combinations of a two-digit lock. *)
TwoDigitLock ==
    "Finish exercise 2."

ASSUME
    /\ (0..9) \X (0..9) = TwoDigitLock
    /\ {<<n,m>> : n,m \in 10..19} \notin SUBSET TwoDigitLock

(* 3. All combinations of a three-digit lock. *)
ThreeDigitLock ==
    "Finish exercise 3."

ASSUME
    /\ (0..9) \X (0..9) \X (0..9) = ThreeDigitLock
    /\ {<<n,m,o>> : n,m,o \in 10..19} \notin SUBSET ThreeDigitLock

(* 4. All pairs (including repetitions) of the natural numbers. *)
PairsOfNaturals ==
    "Finish exercise 4."

ASSUME
    {<<n,m>> : n,m \in 0..100} \subseteq PairsOfNaturals

(* 5. All triples... *)
TriplesOfNaturals ==
    "Finish exercise 5."

ASSUME
    {<<n,m,o>> : n,m,o \in 0..25} \subseteq TriplesOfNaturals

(* 6. Set of all pairs and triples... *)
PairsAndTriplesOfNaturals ==
    "Finish exercise 6."

ASSUME
    /\ {<<n,m>> : n,m \in 0..100} \subseteq PairsAndTriplesOfNaturals
    /\ {<<n,m,o>> : n,m,o \in 0..25} \subseteq PairsAndTriplesOfNaturals

(* 7. What is the Cardinality of 3. ? *)
Cardinality3 ==
    "Finish exercise 7."

ASSUME Cardinality3 = 1000

(* 8. What is the Cardinality of 6. (PairsAndTriplesOfNaturals) ? *)

--------------------------------------------------------------

(* 9. The range/image/co-domain of a function. *)
Range(f) == "Finish exercise 9."

ASSUME Range([a |-> 1, b |-> 2, c |-> 3]) = 1..3

(* 10. The permutations of a set _without_ repetition. *)
Perms(S) ==
    "Finish exercise 10."

ASSUME Perms({1,2,3}) =
             {<<1, 2, 3>>, <<1, 3, 2>>,
              <<2, 1, 3>>, <<2, 3, 1>>,
              <<3, 1, 2>>, <<3, 2, 1>>}

Perms2(S) ==
    \* If for all w in S there exists a v in S for which f[v]=w,
    \* there can be no repetitions as a consequence. The predicate
    \* demands for all elements of S to be in the range of f.
    "Finish exercise 10."

ASSUME Perms2({1,2,3}) =
             {<<1, 2, 3>>, <<1, 3, 2>>,
              <<2, 1, 3>>, <<2, 3, 1>>,
              <<3, 1, 2>>, <<3, 2, 1>>}

Perms3(S) ==
    "Finish exercise 10."

ASSUME Perms3({1,2,3}) =
             {<<1, 2, 3>>, <<1, 3, 2>>,
              <<2, 1, 3>>, <<2, 3, 1>>,
              <<3, 1, 2>>, <<3, 2, 1>>}

(* 11. Reverse a sequence (a function with domain 1..N). *)
Reverse(seq) ==
    "Finish exercise 11."

ASSUME Reverse(<<1, 2, 3>>) = <<3, 2, 1>>
ASSUME Reverse(<<>>) = <<>>

(* 12. An (infix) operator to quickly define a function mapping an x to a y.  *)
x :> y ==
    "Finish exercise 12."

ASSUME "x" :> 42 = [ x |-> 42 ]

(* 13. Merge two functions f and g *)
f ++ g ==
  "Finish exercise 13."

ASSUME <<1,2,3>> ++ [i \in 1..6 |-> i] = <<1, 2, 3, 4, 5, 6>>

(* 14. Advanced!!! Inverse of a function f (swap the domain and range). *)
Inverse(f) ==
   "Finish exercise 14."

ASSUME Inverse(("a" :> 0) ++ ("b" :> 1) ++ ("c" :> 2)) =
              ((0 :> "a") ++ (1 :> "b") ++ (2 :> "c"))

==================
