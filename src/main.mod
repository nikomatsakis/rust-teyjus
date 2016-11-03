% PROBLEMS:
%
% I am misusing ! quite a bit below. My intention was to indicate that
% at most one of those rules applies. But in fact it will cut off
% expansions. e.g., `subtype T1 T2 O` yields `T1 = i32` only.  This is
% of course an interesting point because it is precisely the place
% where Prolog's unification meet's Rust's semantics and has trouble.

module main.

accumulate lists.
accumulate sets.
accumulate debug.

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

% Outputs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% The output from the trait matching and type equating process is a
% set of lifetime obligations.

kind t_lt_constraint type.
type lt_constraint_outlives t_lt -> t_lt -> t_lt_constraint.
type lt_constraint_equals t_lt -> t_lt -> t_lt_constraint.

% Relate kinds %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type relate_arg t_variance -> t_arg -> t_arg -> (list t_lt_constraint) -> o.
relate_arg V (arg_ty A) (arg_ty B) O :- relate_ty V A B O.
relate_arg V (arg_lt A) (arg_lt B) O :- relate_ty V (ref A i32) (ref B i32) O.

type relate_args (list t_variance) -> (list t_arg) -> (list t_arg) -> (list t_lt_constraint) -> o.
relate_args nil nil nil nil.
relate_args (V :: Vs) (A :: As) (B :: Bs) O3 :-
    relate_arg V A B O1,
    relate_args Vs As Bs O2,
    join O1 O2 O3.

type eq_args (list t_arg) -> (list t_arg) -> (list t_lt_constraint) -> o.
eq_args nil nil nil.
eq_args (A :: As) (B :: Bs) O3 :-
    relate_arg invariant A B O1,
    eq_args As Bs O2,
    join O1 O2 O3.

% Relate types %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% `relate_ty`: Relate two types by making them equal, subtype,
% supertype, etc as needed.
type relate_ty t_variance -> t_ty -> t_ty -> (list t_lt_constraint) -> o.
relate_ty V i32 i32 nil.
relate_ty V str str nil.
relate_ty V (array T1) (array T2) O :-
    relate_ty V T1 T2 O.
relate_ty V (ref La Ta) (ref Lb Tb) O3 :-
    relate_ty V Ta Tb O1,
    relate_lt V La Lb O2,
    join O1 O2 O3.
relate_ty V (ref_mut La Ta) (ref_mut Lb Tb) O3 :-
    relate_ty invariant Ta Tb O1,
    relate_lt V La Lb O2,
    join O1 O2 O3.
relate_ty V (fn Aa Va) (fn Ab Vb) O3 :-
    invert_variance V Vcontra,
    relate_ty Vcontra Aa Ab O1,
    relate_ty V Va Vb O2,
    join O1 O2 O3.
relate_ty V (tup2 Aa Va) (tup2 Ab Vb) O3 :-
    relate_ty V Aa Ab O1,
    relate_ty V Va Vb O2,
    join O1 O2 O3.

% FIXME define for other variances
%
% Have to be careful here tho or else it goes off on a wild goose
% chase; e.g., `i32 <: ?T` can be solved by `?T = i32` but also `?T =
% for<'a> i32` and so forth (the syntax of our types here isn't
% restricting `for<'a> i32`, but even if we did the same problem would
% presumably arise with `fn(i32)`.
relate_ty invariant (forall A) (forall B) O :-
    pi La \ sigma Lb \ relate_ty V (A La) (B Lb) O,
    sigma La \ pi Lb \ relate_ty V (A La) (B Lb) O.

type relate_lt t_variance -> t_lt -> t_lt -> (list t_lt_constraint) -> o.
relate_lt covariant A B [lt_constraint_outlives A B].
relate_lt contravariant A B [lt_constraint_outlives B A].
relate_lt invariant A B [lt_constraint_equals A B].

type baz string -> string.

type subtype t_ty -> t_ty -> (list t_lt_constraint) -> o.
subtype A B O :- relate_ty covariant A B O.

type eqtype t_ty -> t_ty -> (list t_lt_constraint) -> o.
eqtype A B O :- relate_ty invariant A B O.

% Structs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% One way would be to have each type have a corresponding series of
% declarations, like this.
%
% ```
% type vec t_ty -> t_ty.
% ```
%
% and then a "variance declaration" would look like this:
%
% ```
% relate_ty V (vec A) (vec B) O :-
%     relate_ty V A B O.
% ```
%
% but for now I will take more of a metadata approach. Not sure if
% this is correct really but at the moment I don't see a downside.

kind t_struct type.

kind t_ident type.

type ident string -> t_ident.

type struct t_ident -> (list t_arg) -> t_ty.

type variance t_ident -> (list t_variance) -> o.

relate_ty V0 (struct N As) (struct N Bs) O :-
    variance N V1s,
    map (apply_variance V0) V1s V2s,
    relate_args V2s As Bs O.

% Example interaction:
%
% [main] ?- (subtype (struct (ident "Cell") [arg_ty (ref (lt "a1") i32)]) (struct (ident "Cell") [arg_ty (ref (lt "b1") i32)]) O).
% 
% The answer substitution:
% O = relate_lt invariant (lt "a1") (lt "b1") :: nil
% 
% More solutions (y/n)? y
% 
% no (more) solutions
% 
% [main] ?- (subtype (struct (ident "Vec") [arg_ty (ref (lt "a1") i32)]) (struct (ident "Vec") [arg_ty (ref (lt "b1") i32)]) O).
% 
% The answer substitution:
% O = relate_lt covariant (lt "a1") (lt "b1") :: nil
% 
% More solutions (y/n)? y
% 
% no (more) solutions
% 
% [main] ?- (relate_ty invariant (struct (ident "Vec") [arg_ty (ref (lt "a1") i32)]) (struct (ident "Vec") [arg_ty (ref (lt "b1") i32)]) O).
% 
% The answer substitution:
% O = relate_lt invariant (lt "a1") (lt "b1") :: nil

% Where clauses %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

kind t_wc type.
type wc_trait_holds t_trait_ref -> t_wc.
type wc_trait_project t_trait_ref -> t_item_name -> t_item_value.
type wc_lt_outlives t_lt -> t_lt -> t_wc.
type wc_ty_outlives t_ty -> t_lt -> t_wc.
type wc_for_lt (t_lt -> t_wc) -> t_wc.

type wc_holds t_wc -> (list t_lt_constraint) -> o.
wc_holds (wc_lt_outlives L1 L2) O :- lt_outlives L1 L2 O.
wc_holds (wc_ty_outlives T A) O :- ty_outlives T A O.
wc_holds (wc_trait_holds T) O :- trait_holds T O.
wc_holds (wc_for_lt L) O :- pi L0 \ wc_holds (L L0) O.

type wcs_hold (list t_wc) -> (list t_lt_constraint) -> o.
wcs_hold nil nil.
wcs_hold (W :: Ws) O3 :- wc_holds W O1, wcs_hold Ws O2, join O1 O2 O3.

% Outlives %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type lt_outlives t_lt -> t_lt -> (list t_lt_constraint) -> o.
lt_outlives L1 L2 [lt_constraint_outlives L1 L2].

type ty_outlives t_ty -> t_lt -> (list t_lt_constraint) -> o.
ty_outlives i32 L nil.
ty_outlives str L nil.
ty_outlives (array T) L O :- ty_outlives T L O.
ty_outlives (ref L1 T1) L2 O3 :-
            lt_outlives L1 L2 O1,
            ty_outlives T1 L2 O2,
            join O1 O2 O3.
ty_outlives (ref_mut L1 T1) L2 O3 :-
            lt_outlives L1 L2 O1,
            ty_outlives T1 L2 O2,
            join O1 O2 O3.
ty_outlives (fn Ta Tr) L O :- ty_outlives (tup2 Ta Tr) L O.
ty_outlives (tup2 Ta Tb) L O3 :-
            ty_outlives Ta L O1,
            ty_outlives Tb L O2,
            join O1 O2 O3.
ty_outlives (forall T) L O :-
            pi L1 \ (ty_outlives (T L1) L O).

% Traits %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Let us try more of a metadata approach to start.

kind t_item_name type.
type item_name string -> t_item_name.

kind t_item_value type.
type item_value_ty t_ty -> t_item_value.
type item_value_lt t_lt -> t_item_value.
type item_value_unit t_item_value.

kind t_trait_ref type.
type trait_ref t_ident -> (list t_arg) -> t_trait_ref.

type trait_ref_matches t_trait_ref -> t_trait_ref -> (list t_lt_constraint) -> o.
trait_ref_matches (trait_ref N As) (trait_ref N Bs) O :- eq_args As Bs O.

kind t_impl type.
type impl t_trait_ref -> (list t_wc) -> t_impl.
type impl_forall (t_arg -> t_impl) -> t_impl.

type impl_matches t_trait_ref -> t_impl -> O -> o.
impl_matches A I O :- announce (impl_matches A I O).
impl_matches A (impl B WC1) O3 :-
    trait_ref_matches A B O1,
    wcs_hold WC1 O2,
    join O1 O2 O3.
impl_matches A (impl_forall I) O :-
    sigma (Arg \ impl_matches A (I Arg) O).

type declare_impl t_impl -> o.

% Trait holds %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type trait_holds t_trait_ref -> (list t_lt_constraint) -> o.
trait_holds TraitRef O :- announce (trait_holds TraitRef O).
trait_holds TraitRef O :- declare_impl SomeImpl, impl_matches TraitRef SomeImpl O.

% Examples

type example1 (list t_lt_constraint) -> o.
example1 O :-
         (variance (ident "Vec") [covariant]) =>
         subtype (struct (ident "Vec") [arg_ty (ref (lt "a1") i32)])
                 (struct (ident "Vec") [arg_ty (ref (lt "a2") i32)])
                 O.

type example1b (list t_lt_constraint) -> o.
example1b O :-
         (variance (ident "Cell") [invariant]) =>
         subtype (struct (ident "Cell") [arg_ty (ref (lt "a1") i32)])
                 (struct (ident "Cell") [arg_ty (ref (lt "a2") i32)])
                 O.

% impl<T> Clone for Vec<T> where T: Clone
% impl Clone for i32
% Vec<i32>: Clone
type example2 (list t_lt_constraint) -> o.
example2 O :-
         (variance (ident "Vec") [covariant]) =>
         (declare_impl (impl (trait_ref (ident "Clone") [arg_ty i32]) [])) =>
         (declare_impl (impl_forall T \ impl (trait_ref (ident "Clone")
                                                        [arg_ty (struct (ident "Vec") [T])])
                                             [wc_trait_holds (trait_ref (ident "Clone") [T])])) =>
         (trait_holds (trait_ref (ident "Clone") [arg_ty (struct (ident "Vec") [arg_ty i32])]) O).

% impl<T> Clone for Vec<T> where T: Clone
type example3 (list t_lt_constraint) -> o.
example3 O :-
         (declare_impl (impl (trait_ref (ident "Clone") [arg_ty i32]) [])) =>
         (trait_holds (trait_ref (ident "Clone") [arg_ty i32]) O).
