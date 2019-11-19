(** Abstract syntax of expressions, before they are type-checked. *)

(** De Bruijn index *)
type index = int

(** Expressions *)
type expr = expr' Location.located
and expr' =
  | Var of index
  | Type
  | Prod of (Name.ident * ty) * ty
  | Lambda of (Name.ident * ty option) * expr
  | Apply of expr * expr
  | Ascribe of expr * ty
  | List 
  | Nil 
  | Cons of expr * expr 
  | Append of expr * expr
  | Length of expr
  | Map of expr * expr
  | Nat
  | Zero
  | Suc of expr
  | Plus of expr * expr
  | TimePlus of expr * expr
  | NatInd of expr * (expr * (expr * expr))
  | TimeNatInd of expr * (expr * (expr * (expr * expr)))
  | App of expr
  | Ret of expr
  | Fmap of expr * expr
  | LiftA of expr * expr
  | Eval of expr
  | Time of expr
  | Eq of expr * expr
  | Refl of expr
  | EqInd of expr * (expr * (expr * (expr * expr)))
  | TimeEqInd of expr * (expr * (expr * (expr * (expr * expr))))

(** Types (equal to expressions at this point). *)
and ty = expr

(** Top-level commands. *)
type toplevel = toplevel' Location.located
and toplevel' =
  | TopLoad of toplevel list
  | TopDefinition of Name.ident * expr
  | TopCheck of expr
  | TopEval of expr
  | TopCompare of expr * expr
  | TopAxiom of Name.ident * expr

(** Shift all indices greter than or equal to [n] by [k]. *)
let rec shift n k {Location.data=e'; loc} =
  let e' = shift' n k e' in
  Location.locate ~loc e'

and shift' n k = function

  | Var j -> if j >= n then Var (j + k) else Var j

  | Type -> Type

  | Prod ((x, t), u) ->
     let t = shift_ty n k t
     and u = shift_ty (n + 1) k u in
     Prod ((x, t), u)

  | Lambda ((x, topt), e) ->
     let t = shift_tyopt n k topt
     and e = shift (n + 1) k e in
     Lambda ((x, t), e)

  | Apply (e1, e2) ->
     let e1 = shift n k e1
     and e2 = shift n k e2 in
     Apply (e1, e2)

  | Ascribe (e, t) ->
     let e = shift n k e
     and t = shift_ty n k t in
     Ascribe (e, t)
  
  | List -> List

  | Nil -> Nil

  | Cons (e1, e2) -> Cons (shift n k e1, shift n k e2)

  | Map (e1, e2) -> Map (shift n k e1, shift n k e2)

  | Append (e1, e2) -> Append (shift n k e1, shift n k e2)

  | Length e -> Length (shift n k e)

  | Nat -> Nat

  | Zero -> Zero

  | Suc e -> Suc (shift n k e)

  | Plus (e1, e2) -> Plus (shift n k e1, shift n k e2)

  | TimePlus (e1, e2) -> TimePlus (shift n k e1, shift n k e2)

  | NatInd (e1, (e2, (e3, e4))) ->
    let e1 = shift n k e1
    and e2 = shift n k e2
    and e3 = shift n k e3
    and e4 = shift n k e4 in
    NatInd (e1, (e2, (e3, e4)))

  | TimeNatInd (e1, (e2, (e3, (e4, e5)))) ->
    let e1 = shift n k e1
    and e2 = shift n k e2
    and e3 = shift n k e3
    and e4 = shift n k e4
    and e5 = shift n k e5 in
    TimeNatInd (e1, (e2, (e3, (e4, e5))))

  | App e1 -> App (shift n k e1)

  | Ret e1 -> Ret (shift n k e1)

  | Fmap (e1, e2) ->
    let e1 = shift n k e1
    and e2 = shift n k e2 in
    Fmap (e1, e2)

  | LiftA (e1, e2) ->
    let e1 = shift n k e1
    and e2 = shift n k e2 in
    LiftA (e1, e2)

  | Eval e1 -> Eval (shift n k e1)

  | Time e1 -> Time (shift n k e1)

  | Eq (e1, e2) ->
    let e1 = shift n k e1
    and e2 = shift n k e2 in
    Eq (e1, e2)

  | Refl e1 -> Refl (shift n k e1)

  | EqInd (e1, (e2, (e3, (e4, e5)))) ->
    let e1 = shift n k e1
    and e2 = shift n k e2
    and e3 = shift n k e3
    and e4 = shift n k e4
    and e5 = shift n k e5 in
    EqInd (e1, (e2, (e3, (e4, e5))))

  | TimeEqInd (e1, (e2, (e3, (e4, (e5, e6))))) ->
    let e1 = shift n k e1
    and e2 = shift n k e2
    and e3 = shift n k e3
    and e4 = shift n k e4
    and e5 = shift n k e5
    and e6 = shift n k e6 in
    TimeEqInd (e1, (e2, (e3, (e4, (e5, e6)))))

and shift_ty n k t = shift n k t

and shift_tyopt n k = function
  | None -> None
  | Some t -> Some (shift_ty n k t)