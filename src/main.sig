sig main.

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
exportdef subtype.