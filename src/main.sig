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

kind t_variance type.
type covariant t_variance.
type contravariant t_variance.
type invariant t_variance.

type invert_variance t_variance -> t_variance -> o.
exportdef invert_variance.

kind t_arg type.
type arg_ty t_ty -> t_arg.
type arg_lt t_lt -> t_arg.

kind t_obligation type.

type relate_lt_oblig t_variance -> t_lt -> t_lt -> t_obligation.

type relate_arg t_variance -> t_arg -> t_arg -> (list t_obligation) -> o.
exportdef relate_arg.

type relate_args (list t_variance) -> (list t_arg) -> (list t_arg) -> (list t_obligation) -> o.
exportdef relate_args.

type relate_ty t_variance -> t_ty -> t_ty -> (list t_obligation) -> o.
exportdef relate_ty.

type subtype t_ty -> t_ty -> (list t_obligation) -> o.
exportdef subtype.

type eqtype t_ty -> t_ty -> (list t_obligation) -> o.
exportdef eqtype.

kind t_struct type.

kind t_struct_name type.

type struct_name string -> t_struct_name.

type struct t_struct_name -> (list t_arg) -> t_ty.

exportdef variance t_struct_name -> (list t_variance) -> o.

