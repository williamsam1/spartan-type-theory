(** Concrete syntax as parsed by the parser. *)

(** Parsed expression. *)
type expr = expr' Location.located
and expr' =
  | Var of Name.ident
  | Numeral of int
  | Type
  | Prod of (Name.ident list * ty) list * ty
  | Lambda of (Name.ident list * ty option) list * ty
  | Apply of expr * expr
  | Arrow of expr * expr
  | Ascribe of expr * ty
  | List
  | Nil
  | Cons of expr * expr
  | Length of expr
  | Map of expr * expr
  | Append of expr * expr
  | Nat
  | Zero
  | Suc of expr
  | Plus of expr * expr
  | NatInd of expr * (expr * (expr * expr))
  | TimeNatInd of expr * (expr * (expr * (expr * expr)))
  | Comp of expr
  | Ret of expr
  | Fmap of expr * expr
  | LiftA of expr * expr
  | Eval of expr
  | Time of expr
  | Eq of expr * expr
  | Refl of expr
  | EqInd of expr * (expr * (expr * (expr * expr)))

(** Parsed type (equal to expression). *)
and ty = expr

(** Parsed top-level command. *)
type toplevel = toplevel' Location.located
and toplevel' =
  | TopLoad of string
  | TopDefinition of Name.ident * expr
  | TopCheck of expr
  | TopEval of expr
  | TopCompare of expr * expr
  | TopAxiom of Name.ident * expr
