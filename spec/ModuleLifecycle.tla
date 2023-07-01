---- MODULE ModuleLifecycle ----

EXTENDS Naturals, Sequences

CONSTANT States, InitState, Transitions

VARIABLE state

Init == state = InitState


Next == ∃ t ∈ Transitions : 
            /\ state = t[1]
            /\ state' = t[2]

Spec == Init /\ [][Next]_state

=================================

