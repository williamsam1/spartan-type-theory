(** {1 Spartan type theory} *)

(** De Bruijn index *)
type index

(** Converts an index into an integer. *)
val index_int : index -> int

(** An atom is a primitive symbol. *)
type atom

(** Expression *)
type expr =
  | Bound of index (** de Bruijn index *)
  | Atom of atom (** primitive symbol *)
  | Type (** the type of types *)
  | Prod of (Name.ident * ty) * ty (** dependent product *)
  | Lambda of (Name.ident * ty) * expr (** lambda abstraction *)
  | Apply of expr * expr (** Complication *)
  | List (** list type *)
  | Nil (** empty list *)
  | Cons of expr * expr (** adding one element to a list *)
  | Append of expr * expr (** adding a list at the end of another list *)
  | Length of expr (** length of a list *)
  | Map of expr * expr (** map a function onto a list *)
  | Nat (** natural number type *)
  | Zero (** first natural number *)
  | Suc of expr (** successor natural numbers *)
  | Plus of expr * expr (** primitive addition *)
  | TimePlus of expr * expr (** timing function for primitive addition *)
  | NatInd of expr * (expr * (expr * expr)) (** natural number induction *)
  | TimeNatInd of expr * (expr * (expr * (expr * expr))) (** timing function for natural number induction *)
  | Comp of expr (** computation *)
  | Ret of expr (** return/pure for Comp *)
  | Fmap of expr * expr (** fmap for Comp *)
  | LiftA of expr * expr (** liftA for Comp *)
  | Eval of expr (** evaluation of computation *)
  | Time of expr (** runtime of computation *)
  | Eq of expr * expr (** propositional equality *)
  | Refl of expr (** reflexivity *)
  | EqInd of expr * (expr * (expr * (expr * expr))) (** equality induction *)
  | TimeEqInd of expr * (expr * (expr * (expr * (expr * expr)))) (** timing function for equality induction *)

(** Type *)
and ty = Ty of expr

(** int as a bound expression *)
val index_expr : int -> expr

(** [Type] as a type. *)
val ty_Type : ty

(** [Nat] as a type. *)
val ty_Nat : ty

(** [List] as a type. *)
val ty_List : ty

(** function type [a -> b] *)
val ty_Fun : ty -> ty -> ty

(** nested product type [(x1 : A1) (x2 : A2) ... (xn : An) b] *)
val ty_Prod : Name.ident -> ty -> (Name.ident * ty) list -> ty -> ty

(** nested application [e1 e2 ... en] *)
val multi_apply : expr -> expr list -> expr

(** nested time plus [e1 (+) e2 (+) ... (+) en] *)
val multi_time_plus : expr -> expr list -> expr

(** The name of an atom *)
val atom_name : atom -> Name.ident

val head : expr -> string

(** Print a TT expression *)
val print_expr : ?max_level:Level.t -> penv:Name.ident list -> expr -> Format.formatter -> unit

(** Print a TT type *)
val print_ty : ?max_level:Level.t -> penv:Name.ident list -> ty -> Format.formatter -> unit

(** Create a fresh atom from an identifier. *)
val new_atom : Name.ident -> atom

(** [abstract x e] abstracts atom [x] into bound index [0] in expression [e], or
   into index [lvl] if given. *)
val abstract : ?lvl:index -> atom -> expr -> expr

(** [abstract_ty x t] abstracts atom [x] into bound index [0] in type [t], or
   into index [lvl] if given. *)
val abstract_ty : ?lvl:index -> atom -> ty -> ty

(** [unabstract a e] instantiates de Bruijn index 0 with [a] in expression [e]. *)
val unabstract : atom -> expr -> expr

(** [unabstract_ty a t] instantiates de Bruijn index 0 with [a] in type [t]. *)
val unabstract_ty : atom -> ty -> ty

(** [instantiate ~lvl:k e e'] instantiates deBruijn index [k] with [e] in expression [e']. *)
val instantiate : ?lvl:index -> expr -> expr -> expr

(** [instantiate_ty ~lvl:k e t] instantiates deBruijn index [k] with [e] in type [t]. *)
val instantiate_ty : ?lvl:index -> expr -> ty -> ty