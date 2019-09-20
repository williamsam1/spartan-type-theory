(** Concrete syntax as parsed by the parser. *)

(** Parsed expression. *)
type expr = expr' Location.located
and expr' =
  | Var of Name.ident
  | Type
  | Prod of (Name.ident list * ty) list * ty
  | Lambda of (Name.ident list * ty option) list * ty
  | Apply of expr * expr
  | Arrow of expr * expr
  | Ascribe of expr * ty
  | Nat
  | Zero
  | Suc of expr
  | Plus of expr * expr
  | NatInd of expr * (expr * (expr * expr))
  | App of expr
  | Ret of expr
  | Fmap of expr * expr
  | LiftA of expr * expr
  | Bind of expr * expr
  | Eval of expr
  | Eq of expr * expr
  | Refl of expr

(** Parsed type (equal to expression). *)
and ty = expr

(** Parsed top-level command. *)
type toplevel = toplevel' Location.located
and toplevel' =
  | TopLoad of string
  | TopDefinition of Name.ident * expr
  | TopCheck of expr
  | TopEval of expr
  | TopAxiom of Name.ident * expr
