(** Conversion from parsed syntax to abstract syntax.

    The desugaring phase loads required files (but does not run them),
    it converts variable names to de Bruijn indices, and it converts
    the complex abstractions of [Input] to the simple ones of [Syntax].
*)

(** Desugaring errors *)
type desugar_error =
  | UnknownIdentifier of Name.ident
  | AlreadyDefined of Name.ident

(** The exception signalling a desugaring error*)
exception Error of desugar_error Location.located

(** [error ~loc err] raises the given desugaring error. *)
let error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

(** Print desugaring error. *)
let print_error err ppf =
  match err with
  | UnknownIdentifier x -> Format.fprintf ppf "unknown identifier %t" (Name.print_ident x)
  | AlreadyDefined x -> Format.fprintf ppf "%t is already defined" (Name.print_ident x)

(** A desugaring context is a list of known identifiers, which is used to compute de
   Bruijn indices. *)
type context = Name.ident list

(** Initial empty context *)
let initial = []

(** Add a new identifier to the context. *)
let extend x ctx = x :: ctx

(** Find the de Bruijn index of [x] in the context [ctx]. *)
let index x ctx =
  let rec search k = function
    | [] -> None
    | y :: ys ->
     if x = y then Some k else search (k+1) ys
  in
  search 0 ctx

(** Desugar an expression *)
let rec expr ctx {Location.data=e; Location.loc=loc} =
  match e with

    | Input.Var x ->
       begin match index x ctx with
       | None -> error ~loc (UnknownIdentifier x)
       | Some k -> Location.locate ~loc (Syntax.Var k)
       end

    | Input.Type -> Location.locate ~loc Syntax.Type

    | Input.Prod (a, u) ->
       let ctx, xts = prod_abstraction ctx a in
       let u = ty ctx u in
       List.fold_right
         (fun (x, t) e -> Location.locate ~loc:t.Location.loc (Syntax.Prod ((x, t), e)))
         xts u

    | Input.Arrow (t1, t2) ->
       let t1 = ty ctx t1
       and t2 = ty ctx t2 in
       let t2 = Syntax.shift_ty 0 1 t2 in
       let x = Name.anonymous () in
       Location.locate ~loc (Syntax.Prod ((x, t1), t2))

    | Input.Lambda (a, e) ->
       let ctx, lst = lambda_abstraction ctx a in
       let e = expr ctx e in
       List.fold_right
         (fun (x, topt) e -> Location.locate ~loc (Syntax.Lambda ((x, topt), e)))
         lst e

    | Input.Apply (e1, e2) ->
       let e1 = expr ctx e1
       and e2 = expr ctx e2 in
       Location.locate ~loc (Syntax.Apply (e1, e2))
    
    | Input.List -> Location.locate ~loc Syntax.List

    | Input.Nil -> Location.locate ~loc Syntax.Nil

    | Input.Cons (e1, e2) ->
      let e1 = expr ctx e1
      and e2 = expr ctx e2 in
      Location.locate ~loc (Syntax.Cons (e1, e2))
    
    | Input.Append (e1, e2) ->
      let e1 = expr ctx e1
      and e2 = expr ctx e2 in
      Location.locate ~loc (Syntax.Append (e1, e2))

    | Input.Map (e1, e2) ->
      let e1 = expr ctx e1
      and e2 = expr ctx e2 in
      Location.locate ~loc (Syntax.Map (e1, e2))
    
    | Input.Length e ->
      let e = expr ctx e in
      Location.locate ~loc (Syntax.Length e)

    | Input.Nat -> Location.locate ~loc Syntax.Nat

    | Input.Zero -> Location.locate ~loc Syntax.Zero

    | Input.Suc e ->
      let e = expr ctx e in
      Location.locate ~loc (Syntax.Suc e)

    | Input.Numeral 0 -> 
      Location.locate ~loc (Syntax.Zero)

    | Input.Numeral i -> 
      let e = expr ctx (Location.locate ~loc (Input.Numeral (i-1))) in
      Location.locate ~loc (Syntax.Suc e)

    | Input.Plus (e1, e2) ->
      let e1 = expr ctx e1
      and e2 = expr ctx e2 in
      Location.locate ~loc (Syntax.Plus (e1, e2))

    | Input.NatInd (e1, (e2, (e3, e4))) ->
      let e1 = expr ctx e1
      and e2 = expr ctx e2
      and e3 = expr ctx e3
      and e4 = expr ctx e4 in
      Location.locate ~loc (Syntax.NatInd (e1, (e2, (e3, e4))))

    | Input.TimeNatInd (e1, (e2, (e3, (e4, e5)))) ->
      let e1 = expr ctx e1
      and e2 = expr ctx e2
      and e3 = expr ctx e3
      and e4 = expr ctx e4
      and e5 = expr ctx e5 in
      Location.locate ~loc (Syntax.TimeNatInd (e1, (e2, (e3, (e4, e5)))))

    | Input.Ascribe (e, t) ->
       let e = expr ctx e
       and t = ty ctx t in
       Location.locate ~loc (Syntax.Ascribe (e, t))

    | Input.Comp e1 ->
      let e1 = expr ctx e1 in
      Location.locate ~loc (Syntax.App e1)

    | Input.Ret e1 ->
      let e1 = expr ctx e1 in
      Location.locate ~loc (Syntax.Ret e1)

    | Input.Fmap (e1, e2) ->
      let e1 = expr ctx e1
      and e2 = expr ctx e2 in
      Location.locate ~loc (Syntax.Fmap (e1, e2))

    | Input.LiftA (e1, e2) ->
      let e1 = expr ctx e1
      and e2 = expr ctx e2 in
      Location.locate ~loc (Syntax.LiftA (e1, e2))

    | Input.Eval e1 ->
      let e1 = expr ctx e1 in
      Location.locate ~loc (Syntax.Eval e1)

    | Input.Time e1 ->
      let e1 = expr ctx e1 in
      Location.locate ~loc (Syntax.Time e1)

    | Input.Eq (e1, e2) ->
      let e1 = expr ctx e1
      and e2 = expr ctx e2 in
      Location.locate ~loc (Syntax.Eq (e1, e2))

    | Input.Refl e1 ->
      let e1 = expr ctx e1 in
      Location.locate ~loc (Syntax.Refl e1)

    | Input.EqInd (e1, (e2, (e3, (e4, e5)))) ->
      let e1 = expr ctx e1
      and e2 = expr ctx e2
      and e3 = expr ctx e3
      and e4 = expr ctx e4
      and e5 = expr ctx e5 in
      Location.locate ~loc (Syntax.EqInd (e1, (e2, (e3, (e4, e5)))))


(** Desugar a type, which at this stage is the same as an expressions. *)
and ty ctx t = expr ctx t

(** Desugar an optional type. *)
and tyopt ctx = function
  | None -> None
  | Some t -> Some (ty ctx t)

(** Desugar a product abstraction. *)
and prod_abstraction ctx a : context * (Name.ident * Syntax.ty) list =
  let rec fold ctx = function
    | [] -> ctx, []
    | (xs, t) :: lst ->
       let ctx, xts = prod_abstraction1 ctx xs t in
       let ctx, yts = fold ctx lst in
       ctx, xts @ yts
  in
  fold ctx a

(** Auxiliary function used to desugar product abstractions. *)
and prod_abstraction1 ctx xs t : context * (Name.ident * Syntax.ty) list =
  let rec fold ctx t lst = function
    | [] -> ctx, List.rev lst
    | x :: xs ->
       let ctx = extend x ctx
       and lst = (x, t) :: lst
       and t = Syntax.shift_ty 0 1 t in
       fold ctx t lst xs
  in
  let t = ty ctx t in
  fold ctx t [] xs

(** Desugar a lambda abstraction. *)
and lambda_abstraction ctx a : context * (Name.ident * Syntax.ty option) list =
  let rec fold ctx = function
    | [] -> ctx, []
    | (xs, t) :: lst ->
       let ctx, xts = lambda_abstraction1 ctx xs t in
       let ctx, yts = fold ctx lst in
       ctx, xts @ yts
  in
  fold ctx a

(** Auxiliary function used to desugar lambda abstractions. *)
and lambda_abstraction1 ctx xs t : context * (Name.ident * Syntax.ty option) list =
  let rec fold ctx t lst = function
    | [] -> ctx, List.rev lst
    | x :: xs ->
       let ctx = extend x ctx
       and lst = (x, t) :: lst
       and t = Syntax.shift_tyopt 0 1 t in
       fold ctx t lst xs
  in
  let t = tyopt ctx t in
  fold ctx t [] xs


(** Desugar a toplevel. *)
let rec toplevel ctx {Location.data=c; Location.loc=loc} =

(** Desugar a non-located toplevel. *)
let toplevel' ctx = function

    | Input.TopLoad fn ->
       let ctx, cmds = load ctx fn in
       ctx, Syntax.TopLoad cmds

    | Input.TopDefinition (x, e) ->
       begin match index x ctx with
       | Some _ -> error ~loc (AlreadyDefined x)
       | None ->
          let e = expr ctx e
          and ctx = extend x ctx in
          ctx, Syntax.TopDefinition (x, e)
       end

    | Input.TopCheck e ->
       let e = expr ctx e in
       ctx, Syntax.TopCheck e

    | Input.TopEval e ->
       let e = expr ctx e in
       ctx, Syntax.TopEval e

    | Input.TopCompare (e1, e2) ->
       let e1 = expr ctx e1
       and e2 = expr ctx e2 in
       ctx, Syntax.TopCompare (e1, e2)

    | Input.TopAxiom (x, t) ->
       let t = ty ctx t in
       let ctx = extend x ctx in
       ctx, Syntax.TopAxiom (x, t)

  in
  let ctx, c = toplevel' ctx c in
  ctx, Location.locate ~loc c

(** Load a file and desugar it. *)
and load ctx fn =
  let cmds = Lexer.read_file Parser.file fn in
  let ctx, cmds = List.fold_left
                    (fun (ctx,cmds) cmd ->
                      let ctx, cmd = toplevel ctx cmd in
                      (ctx, cmd::cmds))
                    (ctx,[]) cmds
  in
  let cmds = List.rev cmds in
  ctx, cmds
