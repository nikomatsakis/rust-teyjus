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

kind t_variance type.
type covariant t_variance.
type contravariant t_variance.
type invariant t_variance.

kind t_arg type.
type arg_ty t_ty -> t_arg.
type arg_lt t_lt -> t_arg.

type apply_variance t_variance -> t_variance -> t_variance -> o.
apply_variance covariant V V :- !.
apply_variance contravariant V S :- !, invert_variance V S.
apply_variance invariant V invariant :- !.

type invert_variance t_variance -> t_variance -> o.
invert_variance covariant contravariant.
invert_variance contravariant covariant.
invert_variance invariant invariant.

% Obligations %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

kind t_obligation type.

% Relate the regions as would be required to make two references have
% the appropriate type. That is, `(relate_lt_oblig covariant A B)` means `A:
% B` in Rust terms, or `B <= A` in terms of the region lattice.
type relate_lt_oblig t_variance -> t_lt -> t_lt -> t_obligation.

% Relate kinds %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type relate_arg t_variance -> t_arg -> t_arg -> (list t_obligation) -> o.
relate_arg V (arg_ty A) (arg_ty B) O :- !, relate_ty V A B O.
relate_arg V (arg_lt A) (arg_lt B) O :- !, relate_ty V (ref A i32) (ref B i32) O.

type relate_args (list t_variance) -> (list t_arg) -> (list t_arg) -> (list t_obligation) -> o.
relate_args nil nil nil nil :- !.
relate_args (V :: Vs) (A :: As) (B :: Bs) O3 :-
    !,
    relate_arg V A B O1,
    relate_args Vs As Bs O2,
    join O1 O2 O3.

% Relate types %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% `relate_ty`: Relate two types by making them equal, subtype,
% supertype, etc as needed.
type relate_ty t_variance -> t_ty -> t_ty -> (list t_obligation) -> o.
relate_ty V i32 i32 nil :- !.
relate_ty V str str nil :- !.
relate_ty V (array T1) (array T2) O :-
    !,
    relate_ty V T1 T2 O.
relate_ty V (ref La Ta) (ref Lb Tb) O2 :-
    !,
    relate_ty V Ta Tb O1,
    set_add (relate_lt_oblig V La Lb) O1 O2.
relate_ty V (ref_mut La Ta) (ref_mut Lb Tb) O2 :-
    !,
    relate_ty invariant Ta Tb O1,
    set_add (relate_lt_oblig V La Lb) O1 O2.
relate_ty V (fn Aa Va) (fn Ab Vb) O3 :-
    !,
    invert_variance V Vcontra,
    relate_ty Vcontra Aa Ab O1,
    relate_ty V Va Vb O2,
    join O1 O2 O3.
relate_ty V (tup2 Aa Va) (tup2 Ab Vb) O3 :-
    !,
    relate_ty V Aa Ab O1,
    relate_ty V Va Vb O2,
    join O1 O2 O3.
relate_ty V (forall A) B O :-
    !,
    sigma L \ relate_ty V (A L) B O.
relate_ty V A (forall B) O :-
    !,
    pi L \ relate_ty V A (B L) O.

type subtype t_ty -> t_ty -> (list t_obligation) -> o.
subtype A B O :- relate_ty covariant A B O.

type eqtype t_ty -> t_ty -> (list t_obligation) -> o.
eqtype A B O :- relate_ty invariant A B O.

% Example type %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% One way would be to have each type have a corresponding series of
% declarations, like this.

type vec t_ty -> t_ty.

% Effectively a variance declaration:
relate_ty V (vec A) (vec B) O :-
    !,
    relate_ty V A B O.

% Another way would be more of a metadata approach.

kind t_struct type.

kind t_struct_name type.

type struct_name string -> t_struct_name.

type struct t_struct_name -> (list t_arg) -> t_ty.

type variance t_struct_name -> (list t_variance) -> o.

relate_ty V0 (struct N As) (struct N Bs) O :-
    !,
    variance N V1s,
    map (apply_variance V0) V1s V2s,
    relate_args V2s As Bs O.

variance (struct_name "Vec") [covariant].
variance (struct_name "Cell") [invariant].