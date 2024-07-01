---- MODULE sys ----
EXTENDS TLC, Integers

\* This system follows the running example of the Cav'23 paper.


Alphabet == {"a", "b"}


VARIABLES aConsumed, bConsumed
vars == <<aConsumed, bConsumed>>

ConsumeA(input) ==
    /\ input = "a"
    /\ aConsumed' = aConsumed + 1
    /\ UNCHANGED bConsumed

\* This alphabet recognizes b but refuses to consume it.
\* Therefore, b can never be consumed in the composed system / environment

\* NOTE: in order to work with TLC, we modify the system slightly to allow eventual deadlock.
\* QUESTION: do we have to model check to initialize?
ConsumeB(input) ==
    /\ input = "b"
    /\ bConsumed > 0
    /\ UNCHANGED vars

Init ==
    /\ aConsumed = 0
    /\ bConsumed = 0

Next == \E input \in Alphabet:
    \/ ConsumeA(input)
    \/ ConsumeB(input)

Spec == Init /\ [][Next]_vars

Safety == aConsumed < 3 /\ bConsumed = 0

====


