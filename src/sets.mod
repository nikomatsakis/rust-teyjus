module sets.

accumulate lists.

type set_add A -> (list A) -> (list A) -> o.

set_add E S1 S2 :- join (E :: nil) S1 S2.
