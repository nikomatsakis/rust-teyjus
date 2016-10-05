module main.

accumulate lists.
accumulate sets.

% Base definitions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

kind rs_ty type.
kind rs_lt type.
kind rs_trait type.

kind obligation type.

type i32 rs_ty. /* i32 */
type str rs_ty. /* str */
type array rs_ty -> rs_ty. /* [T] */
type ref rs_lt -> rs_ty -> rs_ty. /* &'a T */
type ref_mut rs_lt -> rs_ty -> rs_ty. /* &'a mut T */
type fn rs_ty -> rs_ty -> rs_ty. /* fn(A) -> T */
type tup2 rs_ty -> rs_ty -> rs_ty. /* (T, U) */
type forall (rs_lt -> rs_ty) -> rs_ty. /* for<'a> T */

type lt string -> rs_lt.

% Relate the regions as would be required to make two references have
% the appropriate type. That is, `(relate_lt_oblig sub A B)` means `A:
% B` in Rust terms, or `B <= A` in terms of the region lattice.
type relate_lt_oblig relation -> rs_lt -> rs_lt -> obligation.

kind relation type.
type sub relation.
type sup relation.
type eq relation.

type invert_relation relation -> relation -> o.
invert_relation sub sup.
invert_relation sup sub.
invert_relation eq eq.

% Relate types %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% `relate_ty`: Relate two types by making them equal, subtype,
% supertype, etc as needed.
type relate_ty relation -> rs_ty -> rs_ty -> (list obligation) -> o.
relate_ty R i32 i32 nil :- !.
relate_ty R str str nil :- !.
relate_ty R (array T1) (array T2) O :-
        !,
        relate_ty R T1 T2 O.
relate_ty R (ref La Ta) (ref Lb Tb) O2 :-
        !,
        relate_ty R Ta Tb O1,
        set_add (relate_lt_oblig R La Lb) O1 O2.
relate_ty R (ref_mut La Ta) (ref_mut Lb Tb) O2 :-
        !,
        relate_ty eq Ta Tb O1,
        set_add (relate_lt_oblig R La Lb) O1 O2.
relate_ty R (fn Aa Ra) (fn Ab Rb) O3 :-
        !,
        invert_relation R Rcontra,
        relate_ty Rcontra Aa Ab O1,
        relate_ty R Ra Rb O2,
        join O1 O2 O3.
relate_ty R (tup2 Aa Ra) (tup2 Ab Rb) O3 :-
        !,
        relate_ty R Aa Ab O1,
        relate_ty R Ra Rb O2,
        join O1 O2 O3.
relate_ty R (forall A) B O :-
        !,
        sigma L \ relate_ty R (A L) B O.
relate_ty R A (forall B) O :-
        !,
        pi L \ relate_ty R A (B L) O.

type subtype rs_ty -> rs_ty -> (list obligation) -> o.
subtype A B O :- relate_ty sub A B O.

type eqtype rs_ty -> rs_ty -> (list obligation) -> o.
eqtype A B O :- relate_ty sub A B O.

% Trait system %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

