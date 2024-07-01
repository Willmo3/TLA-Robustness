---- MODULE env ----
EXTENDS TLC, Integers

\* This env follows the running example of the Cav'23 paper.


Alphabet == {"a", "b"}


\* State: what state we're currently in
\* aConsumed: how many as have been consumed
\* bConsumed: how many b inputs have been consumed
VARIABLES aConsumed, bConsumed
vars == <<aConsumed, bConsumed>>

ConsumeA(input) == 
    /\ input = "a"
    /\ aConsumed = 0
    /\ aConsumed' = 1
    /\ UNCHANGED bConsumed

ConsumeB(input) == 
    /\ input = "b"
    /\ aConsumed = 1
    /\ bConsumed = 0
    /\ bConsumed' = bConsumed + 1
    /\ UNCHANGED aConsumed

\* Deadlock after this

Init ==
    /\ aConsumed = 0
    /\ bConsumed = 0

Next == \E input \in Alphabet:
    \/ ConsumeA(input)
    \/ ConsumeB(input)

Spec == Init /\ [][Next]_vars

====