---- MODULE EventBus ----

EXTENDS Naturals, Sequences

CONSTANT Modules, Events, InitEvents

VARIABLE events

Init == events = InitEvents

Send(m, e) == /\ m ∈ Modules
               /\ e ∈ Events
               /\ events' = Append(events, <<m, e>>)

Next == ∃ m ∈ Modules, e ∈ Events : Send(m, e)


Spec == Init /\ [][Next]_events

=================================
