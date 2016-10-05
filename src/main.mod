module main.

accumulate lists.
accumulate sets.

kind rs_ty type.
kind rs_lt type.

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

type lt_outlives rs_lt -> rs_lt -> obligation.

type subtype rs_ty -> rs_ty -> (list obligation) -> o.
subtype i32 i32 nil.
subtype str str nil.
subtype (array T1) (array T2) O :-
        subtype T1 T2 O.
subtype (ref La Ta) (ref Lb Tb) O2 :-
        subtype Ta Tb O1,
        set_add (lt_outlives La Lb) O1 O2.
subtype (ref_mut La T) (ref_mut Lb T) [lt_outlives La Lb].
subtype (fn Aa Ra) (fn Ab Rb) O3 :-
        subtype Ab Aa O1,
        subtype Ra Rb O2,
        join O1 O2 O3.
subtype (tup2 Aa Ra) (tup2 Ab Rb) O3 :-
        subtype Aa Ab O1,
        subtype Ra Rb O2,
        join O1 O2 O3.
subtype (forall A) B O :-
        sigma L \ subtype (A L) B O.
subtype A (forall B) O :-
        pi L \ subtype A (B L) O.

