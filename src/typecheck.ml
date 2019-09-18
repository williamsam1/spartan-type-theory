(** Spartan type checking. *)

(** Type errors *)
type type_error =
  | InvalidIndex of int
  | TypeExpected of TT.ty * TT.ty
  | TypeExpectedButFunction of TT.ty
  | FunctionExpected of TT.ty
  | AppExpected of TT.ty
  | CannotInferArgument of Name.ident

exception Error of type_error Location.located

(** [error ~loc err] raises the given type-checking error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

let print_error ~penv err ppf =
  match err with

  | InvalidIndex k -> Format.fprintf ppf "invalid de Bruijn index %d, please report" k

  | TypeExpected (ty_expected, ty_actual) ->
     Format.fprintf ppf "this expression should have type %t but has type %t"
                        (TT.print_ty ~penv ty_expected)
                        (TT.print_ty ~penv ty_actual)

  | TypeExpectedButFunction ty ->
     Format.fprintf ppf "this expression is a function but should have type %t"
                        (TT.print_ty ~penv ty)

  | FunctionExpected ty ->
     Format.fprintf ppf "this expression should be a function but has type %t"
                        (TT.print_ty ~penv ty)

  | AppExpected ty ->
     Format.fprintf ppf "this expression should be an App but has type %t"
                        (TT.print_ty ~penv ty)

  | CannotInferArgument x ->
     Format.fprintf ppf "cannot infer the type of %t" (Name.print_ident x)

(** [infer ctx e] infers the type [ty] of expression [e]. It returns
    the processed expression [e] and its type [ty].  *)
let rec infer ctx {Location.data=e'; loc} =
  match e' with

  | Syntax.Var k ->
     begin
       match Context.lookup k ctx with
       | None -> error ~loc (InvalidIndex k)
       | Some (a, t) -> TT.Atom a, t
     end

  | Syntax.Type ->
     TT.Type, TT.ty_Type

  | Syntax.Prod ((x, t), u) ->
     let t = check_ty ctx t in
     let x' = TT.new_atom x in
     let ctx = Context.extend_ident x' t ctx in
     let u = check_ty ctx u in
     let u = TT.abstract_ty x' u in
     TT.Prod ((x, t), u),
     TT.ty_Type

  | Syntax.Lambda ((x, Some t), e) ->
     let t = check_ty ctx t in
     let x' = TT.new_atom x in
     let ctx  = Context.extend_ident x' t ctx in
     let e, u = infer ctx e in
     let e = TT.abstract x' e in
     let u = TT.abstract_ty x' u in
     TT.Lambda ((x, t), e),
     TT.Ty (TT.Prod ((x, t), u))

  | Syntax.Lambda ((x, None), _) ->
     error ~loc (CannotInferArgument x)

  | Syntax.Apply (e1, e2) ->
     let e1, t1 = infer ctx e1 in
     begin
       match Equal.as_prod ctx t1 with
       | None -> error ~loc (FunctionExpected t1)
       | Some ((x, t), u) ->
          let e2 = check ctx e2 t in
          TT.Apply (e1, e2),
          TT.instantiate_ty e2 u
     end

  | Syntax.Ascribe (e, t) ->
     let t = check_ty ctx t in
     let e = check ctx e t in
     e, t

  | Syntax.Nat -> TT.Nat, TT.ty_Type

  | Syntax.Zero -> TT.Zero, TT.ty_Nat

  | Syntax.Suc e ->
    let e = check ctx e TT.ty_Nat in
    TT.Suc e, TT.ty_Nat

  | Syntax.Plus (e1, e2) ->
    let e1 = check ctx e1 TT.ty_Nat in
    let e2 = check ctx e2 TT.ty_Nat in
    TT.Plus (e1, e2), TT.ty_Nat

  | Syntax.NatInd (e1, (e2, (e3, e4))) ->
    let e1 = check ctx e1 (TT.ty_Fun TT.ty_Nat TT.ty_Type) in
    let e2 = check ctx e2 (TT.Ty (TT.Apply (e1, TT.Zero))) in
    let var_n = Name.Ident ("n", Name.Word) in
    let x = Name.anonymous () in
    let nat_n = TT.index_expr 0 in
    let nat_n2 = TT.index_expr 1 in
    let t = TT.ty_Prod var_n TT.ty_Nat [(x, TT.Ty (TT.Apply (e1, nat_n)))] (TT.Ty (TT.Apply (e1, TT.Suc nat_n2))) in
    let e3 = check ctx e3 t in
    let e4 = check ctx e4 TT.ty_Nat in
    TT.NatInd (e1, (e2, (e3, e4))),
    TT.Ty (TT.Apply (e1, e4))

  | Syntax.App e1 ->
    let e1 = check ctx e1 TT.ty_Type in
    TT.App e1, TT.ty_Type

  | Syntax.Ret e1 ->
    let e1, TT.Ty t1 = infer ctx e1 in
    TT.Ret e1, TT.Ty (TT.App t1)

  | Syntax.Fmap (e1, e2) ->
    let e1, t1 = infer ctx e1 in
    begin
      match Equal.as_prod ctx t1 with
      | None -> error ~loc (FunctionExpected t1)
      | Some ((x, TT.Ty t), TT.Ty u) ->
        let e2 = check ctx e2 (TT.Ty (TT.App t)) in
          TT.Fmap (e1, e2),
          TT.Ty (TT.App (TT.instantiate (TT.Eval e2) u))
    end

  | Syntax.LiftA (e1, e2) ->
    let e1, t1 = infer ctx e1 in
    begin
      match Equal.as_app ctx t1 with
      | None -> error ~loc (AppExpected t1)
      | Some t1 ->
        begin
          match Equal.as_prod ctx (TT.Ty t1) with
          | None -> error ~loc (FunctionExpected (TT.Ty t1))
          | Some ((x, TT.Ty t), TT.Ty u) ->
            let e2 = check ctx e2 (TT.Ty (TT.App t)) in
              TT.LiftA (e1, e2),
              TT.Ty (TT.App (TT.instantiate (TT.Eval e2) u))
        end
    end

  | Syntax.Bind (e1, e2) ->
    let e1, t1 = infer ctx e1 in
    begin
      match Equal.as_prod ctx t1 with
      | None -> error ~loc (FunctionExpected t1)
      | Some ((x, TT.Ty t), TT.Ty u) ->
        begin
          match u with
          | TT.App u -> 
            let e2 = check ctx e2 (TT.Ty (TT.App t)) in
              TT.Bind (e1, e2),
              TT.Ty (TT.App (TT.instantiate (TT.Eval e2) u))
          | _ -> error ~loc (AppExpected (TT.Ty u))
        end
    end

  | Syntax.Eval e1 ->
    let e1, t1 = infer ctx e1 in
    begin
       match Equal.as_app ctx t1 with
       | None -> error ~loc (AppExpected t1)
       | Some t1 -> TT.Eval e1, TT.Ty t1
     end

(** [check ctx e ty] checks that [e] has type [ty] in context [ctx].
    It returns the processed expression [e]. *)
and check ctx ({Location.data=e'; loc} as e) ty =
  match e' with

  | Syntax.Lambda ((x, None), e) ->
     begin
       match Equal.as_prod ctx ty with
       | None -> error ~loc (TypeExpectedButFunction ty)
       | Some ((x, t), u) ->
          let x' = TT.new_atom x in
          let ctx = Context.extend_ident x' t ctx
          and u = TT.unabstract_ty x' u in
          check ctx e u
     end

  | Syntax.Lambda ((_, Some _), _)
  | Syntax.Apply _
  | Syntax.Prod _
  | Syntax.Var _
  | Syntax.Type
  | Syntax.Nat
  | Syntax.Zero
  | Syntax.Suc _
  | Syntax.Plus _
  | Syntax.NatInd _
  | Syntax.App _
  | Syntax.Ret _
  | Syntax.Fmap _
  | Syntax.LiftA _
  | Syntax.Bind _
  | Syntax.Eval _
  | Syntax.Ascribe _ ->
     let e, ty' = infer ctx e in
     if Equal.ty ctx ty ty'
     then
       e
     else
       error ~loc (TypeExpected (ty, ty'))


(** [check_ty ctx t] checks that [t] is a type in context [ctx]. It returns the processed
   type [t]. *)
and check_ty ctx t =
  let t = check ctx t TT.ty_Type in
  TT.Ty t

let rec toplevel ~quiet ctx {Location.data=tc; loc} =
  let ctx = toplevel' ~quiet ctx tc in
  ctx

and toplevel' ~quiet ctx = function

  | Syntax.TopLoad lst ->
     topfile ~quiet ctx lst

  | Syntax.TopDefinition (x, e) ->
     let e, ty = infer ctx e in
     let x' = TT.new_atom x in
     let ctx = Context.extend_ident x' ty ctx in
     let ctx = Context.extend_def x' e ctx in
     if not quiet then Format.printf "%t is defined.@." (Name.print_ident x) ;
     ctx

  | Syntax.TopCheck e ->
     let e, ty = infer ctx e in
     Format.printf "@[<hov>%t@]@\n     : @[<hov>%t@]@."
       (TT.print_expr ~penv:(Context.penv ctx) e)
       (TT.print_ty ~penv:(Context.penv ctx) ty) ;
     ctx

  | Syntax.TopEval e ->
     let e, ty = infer ctx e in
     let e = Equal.norm_expr ~strategy:Equal.CBV ctx e in
     Format.printf "@[<hov>%t@]@\n     : @[<hov>%t@]@."
       (TT.print_expr ~penv:(Context.penv ctx) e)
       (TT.print_ty ~penv:(Context.penv ctx) ty) ;
     ctx

  | Syntax.TopAxiom (x, ty) ->
     let ty = check_ty ctx ty in
     let x' = TT.new_atom x in
     let ctx = Context.extend_ident x' ty ctx in
     if not quiet then Format.printf "%t is assumed.@." (Name.print_ident x) ;
     ctx

and topfile ~quiet ctx lst =
  let rec fold ctx = function
    | [] -> ctx
    | top_cmd :: lst ->
       let ctx = toplevel ~quiet ctx top_cmd in
       fold ctx lst
  in
  fold ctx lst
