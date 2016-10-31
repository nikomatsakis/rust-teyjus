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

kind t_lt_constraint type.

type relate_lt_oblig t_variance -> t_lt -> t_lt -> t_lt_constraint.

type relate_arg t_variance -> t_arg -> t_arg -> (list t_lt_constraint) -> o.
exportdef relate_arg.

type relate_args (list t_variance) -> (list t_arg) -> (list t_arg) -> (list t_lt_constraint) -> o.
exportdef relate_args.

type relate_ty t_variance -> t_ty -> t_ty -> (list t_lt_constraint) -> o.
exportdef relate_ty.

type subtype t_ty -> t_ty -> (list t_lt_constraint) -> o.
exportdef subtype.

type eqtype t_ty -> t_ty -> (list t_lt_constraint) -> o.
exportdef eqtype.

% Structs %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

kind t_struct type.

kind t_ident type.

type ident string -> t_ident.

type struct t_ident -> (list t_arg) -> t_ty.

exportdef variance t_ident -> (list t_variance) -> o.

% Where clauses %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

kind t_wc type.
type t_wc_trait_project t_trait_ref -> t_item_name -> t_item_value.
type t_wc_lt_outlives t_lt -> t_lt -> t_wc.
type t_wc_ty_outlives t_ty -> t_lt -> t_wc.

exportdef wc_holds t_wc -> (list t_lt_constraint) -> o.

exportdef wcs_hold (list t_wc) -> (list t_lt_constraint) -> o.

% Traits %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

kind t_item_name type.
type item_name string -> t_item_name.

kind t_item_value type.
type item_value_ty t_ty -> t_item_value.
type item_value_lt t_lt -> t_item_value.
type item_value_unit t_item_value.

kind t_trait_ref type.
type trait_ref t_ident -> (list t_arg) -> t_trait_ref.

exportdef trait_ref_matches t_trait_ref -> t_trait_ref -> (list t_lt_constraint) -> o.

kind t_impl type.
type impl t_trait_ref -> (list t_wc) -> t_impl.
type impl_forall (t_arg -> t_impl) -> t_impl.

exportdef impl_matches t_trait_ref -> t_impl -> O -> o.
