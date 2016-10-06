module main.

accumulate lists.
accumulate sets.

% Base definitions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

kind t_lt type.
type lt string -> t_lt.

kind t_ty type.
type i32 t_ty. /* i32 */
type str t_ty. /* str */
type array t_ty -> t_ty. /* [T] */
type ref t_lt -> t_ty -> t_ty. /* &'a T */
type ref_mut t_lt -> t_ty -> t_ty. /* &'a mut T */
type fn t_ty -> t_ty -> t_ty. /* fn(A) -> T */
type tup2 t_ty -> t_ty -> t_ty. /* (T, U) */
type forall (t_lt -> t_ty) -> t_ty. /* for<'a> T */

kind t_relation type.
type sub t_relation.
type sup t_relation.
type eq t_relation.

type invert_relation t_relation -> t_relation -> o.
invert_relation sub sup.
invert_relation sup sub.
invert_relation eq eq.

kind rs_arg type.
type arg_ty t_ty -> rs_arg.
type arg_lt t_lt -> rs_arg.

% Obligations %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

kind t_obligation type.

% Relate the regions as would be required to make two references have
% the appropriate type. That is, `(relate_lt_oblig sub A B)` means `A:
% B` in Rust terms, or `B <= A` in terms of the region lattice.
type relate_lt_oblig t_relation -> t_lt -> t_lt -> t_obligation.

% Relate kinds %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type relate_arg t_relation -> rs_arg -> rs_arg -> (list t_obligation) -> o.
relate_arg R (arg_ty A) (arg_ty B) O :- !, relate_ty R A B O.
relate_arg R (arg_lt A) (arg_lt B) O :- !, relate_ty R (ref A i32) (ref B i32) O.

type relate_args (list t_relation) -> (list rs_arg) -> (list rs_arg) -> (list t_obligation) -> o.
relate_args nil nil nil nil :- !.
relate_args (R :: Rs) (A :: As) (B :: Bs) O3 :-
    !,
    relate_arg R A B O1,
    relate_args Rs As Bs O2,
    join O1 O2 O3.

% Relate types %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% `relate_ty`: Relate two types by making them equal, subtype,
% supertype, etc as needed.
type relate_ty t_relation -> t_ty -> t_ty -> (list t_obligation) -> o.
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

type subtype t_ty -> t_ty -> (list t_obligation) -> o.
subtype A B O :- relate_ty sub A B O.

type eqtype t_ty -> t_ty -> (list t_obligation) -> o.
eqtype A B O :- relate_ty sub A B O.

% Example type %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%type Vec t_ty -> t_ty.
%
%% Effectively a variance declaration:
%relate_ty R (Vec A) (Vec B) O :-
%    !,
%    relate_ty R A B O.
%
%kind rs_struct type.
%kind rs_struct_name type.
%
%type rs_struct_name string -> rs_struct_name.
%
%type rs_struct string -> (list rs_arg) -> t_ty.
%
%type rs_variance 
%relate_ty R (rs_struct N nil) (rs_struct N nil) nil :-
%    !.
%
%relate_ty R (rs_struct N (A :: As)) (rs_struct N (B :: Bs)) O3 :-
%    !,
%    relate_arg R A B O1,
%    relate_ty R A B O1,

