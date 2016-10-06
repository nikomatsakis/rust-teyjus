sig main.

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
exportdef invert_relation.

kind rs_arg type.
type arg_ty t_ty -> rs_arg.
type arg_lt t_lt -> rs_arg.

kind t_obligation type.

type relate_lt_oblig t_relation -> t_lt -> t_lt -> t_obligation.

type relate_arg t_relation -> rs_arg -> rs_arg -> (list t_obligation) -> o.
exportdef relate_arg.

type relate_args (list t_relation) -> (list rs_arg) -> (list rs_arg) -> (list t_obligation) -> o.
exportdef relate_args.

type relate_ty t_relation -> t_ty -> t_ty -> (list t_obligation) -> o.
exportdef relate_ty.

type subtype t_ty -> t_ty -> (list t_obligation) -> o.
exportdef subtype.

type eqtype t_ty -> t_ty -> (list t_obligation) -> o.
exportdef eqtype.
