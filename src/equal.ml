(** Equality and normalization. *)

(** A normalization strategy. *)
type strategy =
  | WHNF (** normalize to weak head-normal form *)
  | CBV (** call-by-value normalization *)

let rec collect_spine sp e =
  match e with
  | TT.Apply (e1, e2) ->
    collect_spine (e2 :: sp) e1
  | _ -> (e, sp)

(** Normalize an addition. *)
let rec eval_plus m n =
  match m with
  | TT.Zero -> n
  | TT.Suc m -> TT.Suc (eval_plus m n)
  | _ -> TT.Plus (m, n)

(** Normalize an expression. *)
let rec norm_expr ~strategy ctx e =
  match e with
  | TT.Bound k -> assert false

  | TT.Type -> e

  | TT.Atom x ->
    begin
      match Context.lookup_def x ctx with
      | None -> e
      | Some e -> norm_expr ~strategy ctx e
    end

  | TT.Prod _ -> e

  | TT.Lambda _ -> e

  | TT.Apply (e1, e2) ->
    let e1 = norm_expr ~strategy ctx e1
    and e2 =
      begin
        match strategy with
        | WHNF -> e2
        | CBV -> norm_expr ~strategy ctx e2
      end
    in
    begin
      match e1 with
      | TT.Lambda (_, e') ->
        let e' = TT.instantiate e2 e' in
        norm_expr ~strategy ctx e'
      | _ -> TT.Apply (e1, e2)
    end

  | TT.Nat -> e

  | TT.Zero -> e

  | TT.Suc e ->
    let n = norm_expr ~strategy ctx e in
    TT.Suc n

  | TT.Plus (e1, e2) ->
    let m = norm_expr ~strategy ctx e1
    and n = norm_expr ~strategy ctx e2 in
    eval_plus m n

  | TT.TimePlus (e1, e2) ->
    let e1 = norm_expr ~strategy ctx e1
    and e2 = norm_expr ~strategy ctx e2 in
    TT.TimePlus (e1, e2)

  | TT.NatInd (t, (a, (f, n))) ->
    let t = norm_expr ~strategy ctx t
    and a = norm_expr ~strategy ctx a
    and f = norm_expr ~strategy ctx f
    and n = norm_expr ~strategy ctx n in
    eval_nat_ind ~strategy ctx t a f n

  | TT.TimeNatInd (k, (t, (a, (f, n)))) ->
    let k = norm_expr ~strategy ctx k
    and t = norm_expr ~strategy ctx t
    and a = norm_expr ~strategy ctx a
    and f = norm_expr ~strategy ctx f
    and n = norm_expr ~strategy ctx n in
    begin
      match k with
      | TT.Zero ->
        begin
          match n with
          | TT.Zero -> TT.Ret TT.Zero
          | TT.Suc n ->
            let t1 = TT.TimeNatInd (k, (t, (a, (f, n))))
            and t2 = TT.Time (TT.LiftA (TT.Fmap (f, TT.Ret n), TT.Ret (TT.NatInd (t, (a, (f, n))))))
            in norm_expr ~strategy ctx (TT.TimePlus (t1, t2))
          | _ -> TT.TimeNatInd (k, (t, (a, (f, n))))
        end
      | TT.Suc k -> norm_expr ~strategy ctx (TT.Time (TT.TimeNatInd (k, (t, (a, (f, n))))))
      | _ ->
        begin
          match n with
          | TT.Zero -> TT.Ret TT.Zero
          | _ -> TT.TimeNatInd (k, (t, (a, (f, n))))
        end
    end

  | TT.Comp e1 ->
    let e1 = norm_expr ~strategy ctx e1 in
    TT.Comp e1

  | TT.Ret e1 ->
    let e1 = norm_expr ~strategy ctx e1 in
    TT.Ret e1

  | TT.Fmap (e1, e2) ->
    let e1 = norm_expr ~strategy ctx e1
    and e2 = norm_expr ~strategy ctx e2 in
    TT.Fmap (e1, e2)

  | TT.LiftA (e1, e2) ->
    let e1 = norm_expr ~strategy ctx e1
    and e2 = norm_expr ~strategy ctx e2 in
    TT.LiftA (e1, e2)

  | TT.Eval e1 ->
    let e1 = norm_expr ~strategy ctx e1 in
    eval_eval ~strategy ctx e1

  | TT.Time e1 ->
    let e1 = norm_expr ~strategy ctx e1 in
    time_eval ~strategy ctx e1

  | TT.Eq (e1, e2) ->
    let e1 = norm_expr ~strategy ctx e1
    and e2 = norm_expr ~strategy ctx e2 in
    TT.Eq (e1, e2)

  | TT.Refl e1 ->
    let e1 = norm_expr ~strategy ctx e1 in
    TT.Refl e1

  | TT.EqInd (a, (r, (e1, (e2, p)))) ->
    let a = norm_expr ~strategy ctx a
    and r = norm_expr ~strategy ctx r
    and e1 = norm_expr ~strategy ctx e1
    and e2 = norm_expr ~strategy ctx e2
    and p = norm_expr ~strategy ctx p in
    begin
      match p with
      | TT.Refl e -> norm_expr ~strategy ctx (TT.Apply (r, e))
      | _ -> TT.EqInd (a, (r, (e1, (e2, p))))
    end

  | TT.TimeEqInd (k, (a, (r, (e1, (e2, p))))) ->
    let k = norm_expr ~strategy ctx k
    and a = norm_expr ~strategy ctx a
    and r = norm_expr ~strategy ctx r
    and e1 = norm_expr ~strategy ctx e1
    and e2 = norm_expr ~strategy ctx e2
    and p = norm_expr ~strategy ctx p in
    begin
      match k with
      | TT.Zero ->
        begin
          match p with
          | TT.Refl e -> norm_expr ~strategy ctx (TT.Time (TT.Fmap (r, TT.Ret e)))
          | _ -> TT.TimeEqInd (k, (a, (r, (e1, (e2, p)))))
        end
      | TT.Suc k -> norm_expr ~strategy ctx (TT.Time (TT.TimeEqInd (k, (a, (r, (e1, (e2, p)))))))
      | _ -> TT.TimeEqInd (k, (a, (r, (e1, (e2, p)))))
    end

(** Normalize a natural number induction. *)
and eval_nat_ind ~strategy ctx t a f n =
  match n with
  | TT.Zero -> a
  | TT.Suc n ->
    let e = TT.Apply (TT.Apply (f, n), eval_nat_ind ~strategy ctx t a f n) in
    norm_expr ~strategy ctx e
  | _ -> TT.NatInd (t, (a, (f, n)))

(** Normalize an evaluation of a computation. *)
and eval_eval ~strategy ctx e =
  match e with
  | TT.Ret e -> e
  | TT.Fmap (e1, e2) ->
    norm_expr ~strategy ctx (TT.Apply (e1, TT.Eval e2))
  | TT.LiftA (e1, e2) ->
    norm_expr ~strategy ctx (TT.Apply (TT.Eval e1, TT.Eval e2))
  | TT.TimePlus (e1, e2) ->
    norm_expr ~strategy ctx (TT.Plus (TT.Eval e1, TT.Eval e2))
  | _ -> TT.Eval e

and time_spine ~strategy ctx e1 sp =
  begin
    match sp with
    | [] -> time_expr ~strategy ctx e1
    | e2 :: sp ->
      begin
        match e1 with
        | TT.Lambda (_, e') ->
          let t1 = TT.Ret (TT.Suc TT.Zero)
          and t2 = time_expr ~strategy ctx e2
          and e2' = norm_expr ~strategy ctx e2 in
          let e' = TT.instantiate e2' e' in
          let t3 = time_spine ~strategy ctx e' sp in
          TT.multi_time_plus t1 [t2 ; t3]
        | _ ->
          let t1 = time_spine_var (TT.Fmap (e1, TT.Ret e2)) sp
          and t2 = time_expr ~strategy ctx e2
          and ts = List.map (time_expr ~strategy ctx) sp in
          TT.multi_time_plus t1 (t2 :: ts) 
      end
  end

and time_spine_var e sp =
  begin
    match sp with
    | [] -> e
    | e2 :: sp -> time_spine_var (TT.LiftA (e, TT.Ret e2)) sp
  end

(** Runtime of a syntactic expression. *)
and time_expr ~strategy ctx e = 
  match e with
  | TT.Bound k -> TT.Ret TT.Zero

  | TT.Type -> TT.Ret TT.Zero

  | TT.Atom x ->
    begin
      match Context.lookup_def x ctx with
      | None -> TT.Ret TT.Zero
      | Some e -> time_expr ~strategy ctx e
    end

  | TT.Prod _ -> TT.Ret TT.Zero

  | TT.Lambda _ -> TT.Ret TT.Zero

  | TT.Apply (e1, e2) ->
    let t1 = time_expr ~strategy ctx e1
    and e1' = norm_expr ~strategy ctx e1
    and t2 = time_expr ~strategy ctx e2
    and e2' = norm_expr ~strategy ctx e2 in
    let (e, sp) = collect_spine [e2'] e1' in
    let t3 = time_spine ~strategy ctx e sp in
    TT.multi_time_plus t1 [t2; t3]

  | TT.Nat -> TT.Ret TT.Zero

  | TT.Zero -> TT.Ret TT.Zero

  | TT.Suc e -> time_expr ~strategy ctx e

  | TT.Plus (e1, e2) -> TT.Ret e1

  | TT.TimePlus (e1, e2) ->
    let t1 = time_expr ~strategy ctx e1
    and t2 = time_expr ~strategy ctx e2 in
    TT.TimePlus (t1, t2)

  | TT.NatInd (t, (a, (f, n))) ->
    let t1 = time_expr ~strategy ctx t
    and t2 = time_expr ~strategy ctx a
    and t3 = time_expr ~strategy ctx f
    and t4 = time_expr ~strategy ctx n
    and t5 = TT.TimeNatInd (TT.Zero, (t, (a, (f, n)))) in
    TT.multi_time_plus t1 [t2; t3; t4; t5]

  | TT.TimeNatInd (k, (t, (a, (f, n)))) ->
    let t1 = time_expr ~strategy ctx k
    and t2 = time_expr ~strategy ctx t
    and t3 = time_expr ~strategy ctx a
    and t4 = time_expr ~strategy ctx f
    and t5 = time_expr ~strategy ctx n
    and t6 = TT.TimeNatInd (TT.Suc k, (t, (a, (f, n)))) in
    TT.multi_time_plus t1 [t2; t3; t4; t5; t6]

  | TT.Comp e1 -> time_expr ~strategy ctx e1

  | TT.Ret e1 -> time_expr ~strategy ctx e1

  | TT.Fmap (e1, e2) ->
    let t1 = time_expr ~strategy ctx e1
    and t2 = time_expr ~strategy ctx e2
    in TT.TimePlus (t1, t2)

  | TT.LiftA (e1, e2) ->
    let t1 = time_expr ~strategy ctx e1
    and t2 = time_expr ~strategy ctx e2 in
    TT.TimePlus (t1, t2)

  | TT.Eval e ->
    let t1 = time_expr ~strategy ctx e
    and e' = norm_expr ~strategy ctx e in
    let t2 = 
      begin
        match e' with
        | TT.Ret e -> time_expr ~strategy ctx e
        | TT.Fmap (e1, e2) -> time_expr ~strategy ctx (TT.Apply (e1, TT.Eval e2))
        | TT.LiftA (e1, e2) -> time_expr ~strategy ctx (TT.Apply (TT.Eval e1, TT.Eval e2))
        | TT.TimePlus (e1, e2) -> time_expr ~strategy ctx (TT.Plus (TT.Eval e1, TT.Eval e2))
        | _ -> assert false
      end in
    TT.TimePlus (t1, t2)

  | TT.Time e1 -> assert false

  | TT.Eq (e1, e2) ->
    let t1 = time_expr ~strategy ctx e1
    and t2 = time_expr ~strategy ctx e2 in
    TT.TimePlus (t1, t2)

  | TT.Refl e1 -> time_expr ~strategy ctx e1

  | TT.EqInd (a, (r, (e1, (e2, p)))) ->
    let t1 = time_expr ~strategy ctx a
    and t2 = time_expr ~strategy ctx r
    and t3 = time_expr ~strategy ctx e1
    and t4 = time_expr ~strategy ctx e2
    and t5 = time_expr ~strategy ctx p
    and t6 = TT.TimeEqInd (TT.Zero, (a, (r, (e1, (e2, p))))) in
    TT.multi_time_plus t1 [t2; t3; t4; t5; t6]

  | TT.TimeEqInd (k, (a, (r, (e1, (e2, p))))) ->
    let t1 = time_expr ~strategy ctx k
    and t2 = time_expr ~strategy ctx a
    and t3 = time_expr ~strategy ctx r
    and t4 = time_expr ~strategy ctx e1
    and t5 = time_expr ~strategy ctx e2
    and t6 = time_expr ~strategy ctx p
    and t7 = TT.TimeEqInd (TT.Zero, (a, (r, (e1, (e2, p))))) in
    TT.multi_time_plus t1 [t2; t3; t4; t5; t6; t7]

(** Normalize the runtime of a computation. *)
and time_eval ~strategy ctx e =
  match e with
  | TT.Ret e -> TT.Ret TT.Zero
  | TT.Fmap (e1, e2) ->
    let t = time_expr ~strategy ctx (TT.Apply (e1, TT.Eval e2)) in
    norm_expr ~strategy ctx t
  | TT.LiftA (e1, e2) ->
    let t = time_expr ~strategy ctx (TT.Apply (TT.Eval e1, TT.Eval e2)) in
    norm_expr ~strategy ctx t
  | TT.TimePlus (e1, e2) ->
    let t = time_expr ~strategy ctx (TT.Plus (TT.Eval e1, TT.Eval e2)) in
    norm_expr ~strategy ctx t
  | _ -> TT.Time e

(** Normalize a type *)
let norm_ty ~strategy ctx (TT.Ty ty) =
  let ty = norm_expr ~strategy ctx ty in
  TT.Ty ty

(** Normalize a type to a product. *)
let as_prod ctx t =
  let TT.Ty t' = norm_ty ~strategy:WHNF ctx t in
  match t' with
  | TT.Prod ((x, t), u) -> Some ((x, t), u)
  | _ -> None

(** Normalize a type to an App type. *)
let as_app ctx t =
  let TT.Ty t' = norm_ty ~strategy:WHNF ctx t in
  match t' with
  | TT.Comp t -> Some t
  | _ -> None

(** [infer_TT ctx e] infers the type [ty] of expression [e]. *)
let rec infer_TT ctx e =
  match e with
  | TT.Bound k ->
     begin
       match Context.lookup (TT.index_int k) ctx with
       | None -> assert false
       | Some (a, t) -> t
     end

  | TT.Atom a ->
    begin
       match Context.lookup_atom_ty a ctx with
       | None -> assert false
       | Some t -> t
     end

  | TT.Type -> TT.ty_Type

  | TT.Prod _ -> TT.ty_Type

  | TT.Lambda ((x, t), e) ->
     let x' = TT.new_atom x in
     let ctx  = Context.extend_ident x' t ctx in
     let u = infer_TT ctx e in
     let u = TT.abstract_ty x' u in
     TT.Ty (TT.Prod ((x, t), u))

  | TT.Apply (e1, e2) ->
     let t1 = infer_TT ctx e1 in
     begin
       match as_prod ctx t1 with
       | None -> assert false
       | Some ((x, t), u) ->
          TT.instantiate_ty e2 u
     end

  | TT.Nat -> TT.ty_Type

  | TT.Zero -> TT.ty_Nat

  | TT.Suc _ -> TT.ty_Nat

  | TT.Plus _ -> TT.ty_Nat

  | TT.TimePlus _ -> TT.Ty (TT.Comp TT.Nat)

  | TT.NatInd (e1, (e2, (e3, e4))) -> TT.Ty (TT.Apply (e1, e4))

  | TT.TimeNatInd _ -> TT.Ty (TT.Comp TT.Nat)

  | TT.Comp _ -> TT.ty_Type

  | TT.Ret e1 ->
    let TT.Ty t1 = infer_TT ctx e1 in
    TT.Ty (TT.Comp t1)

  | TT.Fmap (e1, e2) ->
    let t1 = infer_TT ctx e1 in
    begin
      match as_prod ctx t1 with
      | None -> assert false
      | Some ((x, TT.Ty t), TT.Ty u) ->
        TT.Ty (TT.Comp (TT.instantiate (TT.Eval e2) u))
    end

  | TT.LiftA (e1, e2) ->
    let t1 = infer_TT ctx e1 in
    begin
      match as_app ctx t1 with
      | None -> assert false
      | Some t1 ->
        begin
          match as_prod ctx (TT.Ty t1) with
          | None -> assert false
          | Some ((x, TT.Ty t), TT.Ty u) ->
              TT.Ty (TT.Comp (TT.instantiate (TT.Eval e2) u))
        end
    end

  | TT.Eval e1 ->
    let t1 = infer_TT ctx e1 in
    begin
       match as_app ctx t1 with
       | None -> assert false
       | Some t1 -> TT.Ty t1
     end

  | TT.Time e1 ->
    let t1 = infer_TT ctx e1 in
    begin
       match as_app ctx t1 with
       | None -> assert false
       | Some t1 -> TT.ty_Nat
     end

  | TT.Eq _ -> TT.ty_Type

  | TT.Refl e1 -> TT.Ty (TT.Eq (e1, e1))

  | TT.EqInd (e1, (e2, (e3, (e4, e5)))) ->
    TT.Ty (TT.multi_apply e1 [ e3 ; e4 ; e5 ])

  | TT.TimeEqInd _ -> TT.Ty (TT.Comp TT.Nat)

(** Compare expressions [e1] and [e2] at type [ty]? *)
let rec expr ctx e1 e2 ty =
  (* short-circuit *)
  (e1 == e2) ||
  begin
    (* The type directed phase *)
    let TT.Ty ty' = norm_ty ~strategy:WHNF ctx ty in
    match  ty' with

    | TT.Prod ((x, t), u) ->
      (* Apply function extensionality. *)
      let x' = TT.new_atom x in
      let ctx = Context.extend_ident x' t ctx
      and e1 = TT.Apply (e1, TT.Atom x')
      and e2 = TT.Apply (e2, TT.Atom x')
      and u = TT.unabstract_ty x' u in
      expr ctx e1 e2 u

    | TT.Type
    | TT.Nat
    | TT.Apply _
    | TT.Bound _
    | TT.NatInd _
    | TT.Comp _
    | TT.Eval _
    | TT.Time _
    | TT.Eq _
    | TT.EqInd _
    | TT.Atom _ ->
      (* Type-directed phase is done, we compare normal forms. *)
      let e1 = norm_expr ~strategy:WHNF ctx e1
      and e2 = norm_expr ~strategy:WHNF ctx e2 in
      expr_whnf ctx e1 e2
    
    | TT.Zero
    | TT.Suc _
    | TT.Plus _
    | TT.TimePlus _
    | TT.TimeNatInd _
    | TT.TimeEqInd _
    | TT.Ret _
    | TT.Fmap _
    | TT.LiftA _
    | TT.Refl _
    | TT.Lambda _ ->
      (* A type should never normalize to an abstraction *)
      assert false
  end

(** Structurally compare weak head-normal expressions [e1] and [e2]. *)
and expr_whnf ctx e1 e2 =
  match e1, e2 with

  | TT.Type, TT.Type -> true

  | TT.Nat, TT.Nat -> true

  | TT.Zero, TT.Zero -> true

  | TT.Suc e1, TT.Suc e2 -> expr_whnf ctx e1 e2

  | TT.Plus (e11, e12), TT.Plus (e21, e22) ->
    expr_whnf ctx e11 e21 && expr_whnf ctx e12 e22

  | TT.TimePlus (e11, e12), TT.Plus (e21, e22) ->
    expr_whnf ctx e11 e21 && expr_whnf ctx e12 e22

  | TT.NatInd (e11, (e12, (e13, e14))), TT.NatInd (e21, (e22, (e23, e24))) ->
    let e1 = expr ctx e11 e21 (infer_TT ctx e11)
    and e2 = expr_whnf ctx e12 e22
    and e3 = expr ctx e13 e23 (infer_TT ctx e13)
    and e4 = expr_whnf ctx e14 e24 in
    e1 && e2 && e3 && e4

  | TT.TimeNatInd (k1, (e11, (e12, (e13, e14)))), TT.TimeNatInd (k2, (e21, (e22, (e23, e24)))) ->
    let k = expr_whnf ctx k1 k2
    and e1 = expr ctx e11 e21 (infer_TT ctx e11)
    and e2 = expr_whnf ctx e12 e22
    and e3 = expr ctx e13 e23 (infer_TT ctx e13)
    and e4 = expr_whnf ctx e14 e24 in
    k && e1 && e2 && e3 && e4

  | TT.Comp e1, TT.Comp e2 -> expr_whnf ctx e1 e2

  | TT.Ret e1, TT.Ret e2 -> expr_whnf ctx e1 e2

  | TT.Fmap (e11, e12), TT.Fmap (e21, e22) ->
    expr ctx e11 e21 (infer_TT ctx e11) && expr_whnf ctx e12 e22

  | TT.LiftA (e11, e12), TT.LiftA (e21, e22) ->
    expr_whnf ctx e11 e21 && expr_whnf ctx e12 e22

  | TT.Eval e1, TT.Eval e2 ->
    expr_whnf ctx e1 e2

  | TT.Time e1, TT.Time e2 ->
    expr_whnf ctx e1 e2

  | TT.Eq (e11, e12), TT.Eq (e21, e22) ->
    expr ctx e11 e21 (infer_TT ctx e11) && expr ctx e12 e22 (infer_TT ctx e12)

  | TT.EqInd (e11, (e12, (e13, (e14, e15)))), TT.EqInd (e21, (e22, (e23, (e24, e25)))) ->
    let e1 = expr ctx e11 e21 (infer_TT ctx e11)
    and e2 = expr ctx e12 e22 (infer_TT ctx e12)
    and e3 = expr_whnf ctx e13 e23
    and e4 = expr_whnf ctx e14 e24
    and e5 = expr_whnf ctx e15 e25 in
    e1 && e2 && e3 && e4 && e5

  | TT.TimeEqInd (k1, (e11, (e12, (e13, (e14, e15))))), TT.TimeEqInd (k2, (e21, (e22, (e23, (e24, e25))))) ->
    let k = expr_whnf ctx k1 k2
    and e1 = expr ctx e11 e21 (infer_TT ctx e11)
    and e2 = expr ctx e12 e22 (infer_TT ctx e12)
    and e3 = expr_whnf ctx e13 e23
    and e4 = expr_whnf ctx e14 e24
    and e5 = expr_whnf ctx e15 e25 in
    k && e1 && e2 && e3 && e4 && e5

  | TT.Refl e1, TT.Refl e2 -> expr_whnf ctx e1 e2

  | TT.Bound k1, TT.Bound k2 ->
    (* We should never be in a situation where we compare bound variables,
       as that would mean that we forgot to unabstract a lambda or a product. *)
    assert false

  | TT.Atom x, TT.Atom y -> x = y

  | TT.Prod ((x, t1), u1), TT.Prod ((_, t2), u2)  ->
    ty ctx t1 t2 &&
    begin
      let x' = TT.new_atom x in
      let ctx = Context.extend_ident x' t1 ctx
      and u1 = TT.unabstract_ty x' u1
      and u2 = TT.unabstract_ty x' u2 in
      ty ctx u1 u2
    end

  | TT.Lambda ((x, t1), e1), TT.Lambda ((_, t2), e2)  ->
    (* We should never have to compare two lambdas, as that would mean that the
       type-directed phase did not figure out that these have product types. *)
    assert false

  | TT.Apply (e11, e12), TT.Apply (e21, e22) ->
    let rec collect sp1 sp2 e1 e2 =
      match e1, e2 with
      | TT.Apply (e11, e12), TT.Apply (e21, e22) ->
        collect (e12 :: sp1) (e22 :: sp2) e11 e21
      | _, _ -> ((e1, sp1), (e2, sp2))
    in
    begin
      let ((e1, sp1), (e2, sp2)) = collect [e12] [e22] e11 e21 in
      spine ctx (e1, sp1) (e2, sp2)
    end

  | (TT.Type | TT.Nat | TT.Zero | TT.Suc _ | TT.Plus _ | TT.TimePlus _ | TT.NatInd _ | TT.TimeNatInd _
    | TT.Bound _ | TT.Atom _ | TT.Prod _ | TT.Lambda _ | TT.Apply _ | TT.Comp _ | TT.Ret _ | TT.Fmap _
    | TT.LiftA _ | TT.Eval _ | TT.Time _ | TT.Eq _ | TT.Refl _ | TT.EqInd _ | TT.TimeEqInd _), _ ->
    false

(** Compare two types. *)
and ty ctx (TT.Ty ty1) (TT.Ty ty2) =
  expr ctx ty1 ty2 TT.ty_Type

(** Compare two spines of equal lengths.

    A spine is a nested application of the form [e1 e2 ... en]
*)
and spine ctx (e1, sp1) (e2, sp2) =
  e1 = e2 &&
  begin
    let rec fold ty sp1 sp2 =
      match as_prod ctx ty with
      | None -> assert false
      | Some ((x, t), u) ->
        begin
          match sp1, sp2 with
          | [e1], [e2] -> expr ctx e1 e2 t
          | e1 :: sp1, e2 :: sp2 ->
            expr ctx e1 e2 t &&
            begin
              let u = TT.instantiate_ty e1 u in
              fold u sp1 sp2
            end
          | _, _ ->
            (* We should never be here, as the lengths of the spines should match. *)
            assert false
        end
    in
    let ty = infer_TT ctx e1 in
    fold ty sp1 sp2
  end

