%{
%}

(* Infix operations a la OCaml *)
%token <Name.ident Location.located> PREFIXOP INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4

(* Names *)
%token <Name.ident> NAME
%token UNDERSCORE

(* Parentheses & punctuations *)
%token LPAREN RPAREN PERIOD
%token COLONEQ
%token COMMA COLON DARROW ARROW

(* Expressions *)
%token LET
%token IN
%token TYPE
%token PROD
%token LAMBDA
%token NAT
%token ZERO
%token SUC
%token <int> NUMERAL
%token PLUS
%token NATIND
%token TIMENATIND
%token LIST
%token NIL
%token CONS
%token LENGTH
%token APPEND
%token MAP
%token COMP
%token RET
%token FMAP
%token LIFTA
%token COMPEVAL
%token COMPTIME
%token EQ
%token REFL
%token EQIND

(* Toplevel commands *)

%token <string> QUOTED_STRING
%token LOAD
%token DEFINITION
%token CHECK
%token EVAL
%token COMPARE
%token AXIOM

(* End of input token *)
%token EOF

(* Precedence and fixity of infix operators *)
%left     INFIXOP0
%right    INFIXOP1
%left     INFIXOP2
%left     INFIXOP3
%right    INFIXOP4

%start <Input.toplevel list> file
%start <Input.toplevel> commandline

%%

(* Toplevel syntax *)

file:
  | f=filecontents EOF            { f }

filecontents:
  |                                   { [] }
  | d=topcomp PERIOD ds=filecontents  { d :: ds }

commandline:
  | topcomp PERIOD EOF       { $1 }

(* Things that can be defined on toplevel. *)
topcomp: mark_location(plain_topcomp) { $1 }
plain_topcomp:
  | LOAD fn=QUOTED_STRING                 { Input.TopLoad fn }
  | DEFINITION x=var_name COLONEQ e=term  { Input.TopDefinition (x, e) }
  | CHECK e=term                          { Input.TopCheck e }
  | EVAL e=term                           { Input.TopEval e }
  | COMPARE e1=prefix_term e2=prefix_term { Input.TopCompare (e1, e2) }
  | AXIOM x=var_name COLON e=term         { Input.TopAxiom (x, e) }

(* Main syntax tree *)
term : mark_location(plain_term) { $1 }
plain_term:
  | e=plain_infix_term                          { e }
  | PROD a=prod_abstraction COMMA e=term        { Input.Prod (a, e) }
  | e1=infix_term ARROW e2=term                 { Input.Arrow (e1, e2) }
  | LAMBDA a=lambda_abstraction DARROW e=term   { Input.Lambda (a, e) }
  | LET x=var_name COLON t=term
      COLONEQ e1=term IN e2=term
    {
      let {Location.data=op; loc} = e2 in
      let op = Location.locate ~loc (Input.Lambda ([([x], Some t)], e2)) in
      Input.Apply (op, e1)
    }
  | LET x=var_name COLONEQ e1=term IN e2=term
    {
      let {Location.data=op; loc} = e2 in
      let op = Location.locate ~loc (Input.Lambda ([([x], None)], e2)) in
      Input.Apply (op, e1)
    }
  | e=infix_term COLON t=term                   { Input.Ascribe (e, t) }


  | oploc=prefix e2=prefix_term
    { let {Location.data=op; loc} = oploc in
      let op = Location.locate ~loc (Input.Var op) in
      Input.Apply (op, e2)
    }

infix_term: mark_location(plain_infix_term) { $1 }
plain_infix_term:
  | e=plain_COMP_term { e }
  | e2=infix_term oploc=infix e3=infix_term
    { let {Location.data=op; loc} = oploc in
      let op = Location.locate ~loc (Input.Var op) in
      let e1 = Location.locate ~loc (Input.Apply (op, e2)) in
      Input.Apply (e1, e3)
    }

COMP_term: mark_location(plain_COMP_term) { $1 }
plain_COMP_term:
  | e=plain_prefix_term                   { e }
  | e1=COMP_term e2=prefix_term           { Input.Apply (e1, e2) }
  | SUC e=prefix_term                     { Input.Suc e }
  | PLUS e1=prefix_term e2=prefix_term    { Input.Plus (e1, e2) }
  | CONS e1=prefix_term e2=prefix_term    { Input.Cons (e1, e2) }
  | APPEND e1=prefix_term e2=prefix_term  { Input.Append (e1, e2) }
  | LENGTH e=prefix_term                  { Input.Length e}
  | MAP e1=prefix_term e2=prefix_term     { Input.Map (e1, e2)}
  | NATIND e1=prefix_term e2=prefix_term
    	e3=prefix_term e4=prefix_term       { Input.NatInd (e1, (e2, (e3, e4))) }
  | TIMENATIND e1=prefix_term e2=prefix_term
      e3=prefix_term e4=prefix_term
      e5=prefix_term                      { Input.TimeNatInd (e1, (e2, (e3, (e4, e5)))) }
  | COMP e1=prefix_term                   { Input.Comp e1 }
  | RET e1=prefix_term                    { Input.Ret e1 }
  | FMAP e1=prefix_term e2=prefix_term    { Input.Fmap (e1, e2) }
  | LIFTA e1=prefix_term e2=prefix_term   { Input.LiftA (e1, e2) }
  | COMPEVAL e1=prefix_term               { Input.Eval e1 }
  | COMPTIME e1=prefix_term               { Input.Time e1 }
  | EQ e1=prefix_term e2=prefix_term      { Input.Eq (e1, e2) }
  | REFL e1=prefix_term               	  { Input.Refl e1 }
  | EQIND e1=prefix_term e2=prefix_term
      e3=prefix_term e4=prefix_term
      e5=prefix_term                      { Input.EqInd (e1, (e2, (e3, (e4, e5)))) }

prefix_term: mark_location(plain_prefix_term) { $1 }
plain_prefix_term:
  | e=plain_simple_term                       { e }
  | oploc=prefix e2=prefix_term
    { let {Location.data=op; loc} = oploc in
      let op = Location.locate ~loc (Input.Var op) in
      Input.Apply (op, e2)
    }

(* simple_term : mark_location(plain_simple_term) { $1 } *)
plain_simple_term:
  | LPAREN e=plain_term RPAREN         { e }
  | TYPE                               { Input.Type }
  | NAT                                { Input.Nat }
  | LIST                               { Input.List }
  | NIL                                { Input.Nil  }
  | ZERO                               { Input.Zero }
  | x=var_name                         { Input.Var x }
  | i=NUMERAL                          { Input.Numeral i }

var_name:
  | NAME                     { $1 }
  | LPAREN op=infix RPAREN   { op.Location.data }
  | LPAREN op=prefix RPAREN  { op.Location.data }
  | UNDERSCORE               { Name.anonymous () }

%inline infix:
  | op=INFIXOP0    { op }
  | op=INFIXOP1    { op }
  | op=INFIXOP2    { op }
  | op=INFIXOP3    { op }
  | op=INFIXOP4    { op }

%inline prefix:
  | op=PREFIXOP { op }

lambda_abstraction:
  | xs=nonempty_list(var_name) COLON t=term  { [(xs, Some t)] }
  | xs=nonempty_list(var_name)               { [(xs, None)] }
  | lst=nonempty_list(typed_binder)          { List.map (fun (xs, t) -> (xs, Some t)) lst }

prod_abstraction:
  | xs=nonempty_list(var_name) COLON t=term  { [(xs, t)] }
  | lst=nonempty_list(typed_binder)          { lst }

typed_binder:
  | LPAREN xs=nonempty_list(var_name) COLON t=term RPAREN { (xs, t) }

mark_location(X):
  x=X
  { Location.locate ~loc:(Location.make $startpos $endpos) x }
%%
