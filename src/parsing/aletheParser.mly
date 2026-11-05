%{
    (** Parser for Alethe proofs. Tokens are defined in [AletheTokens] and
        produced by [AletheLexer]. *)

    open Common.Pos
    open AletheSyntax

    let fail lps msg = Common.Error.fatal (Some (locate lps)) "%s" msg
%}

%token EOF
%token LEFTPAR
%token RIGHTPAR
%token COLON
%token ASSIGN
%token RULE
%token STEP
%token CLAUSE
%token PREMISES
%token ARGS
%token ANCHOR
%token ASSUME
%token DEFINEFUN
%token FORALL
%token EXISTS
%token CHOICE
%token LET
%token BANG
%token <string> RATIONAL
%token <string> NEGDECIMAL
%token <string> NEGNUMERAL
%token <string> DECIMAL
%token <string> NUMERAL
%token <string> HEXADECIMAL
%token <string> BINARY
%token <string> STRING
%token <string> SYMBOL

%start line
%type <AletheSyntax.command Common.Pos.loc> line

%%

(* [line] parses one proof command per call, as [DkParser.line] does. *)
line:
  | LEFTPAR c=command RIGHTPAR { make_pos $sloc c }
  | EOF { raise End_of_file }

command:
  | ASSUME name=SYMBOL t=term attrs=attribute* { Assume(name, t, attrs) }
  | STEP id=SYMBOL c=clause COLON RULE r=SYMBOL pa=step_annotations
    { let (premises, (args, attributes)) = pa in
      Step {id; clause = c; rule = r; premises; args; attributes} }
  | ANCHOR COLON STEP id=SYMBOL ca=then_attributes(context)
    { let (ctx, attrs) = ca in Anchor(id, ctx, attrs) }
  | DEFINEFUN f=SYMBOL LEFTPAR xs=sorted_var* RIGHTPAR s=term t=term
    { DefineFun(f, xs, s, t) }

clause:
  | LEFTPAR CLAUSE ts=term* RIGHTPAR { ts }

(* [:premises], [:args] and other attributes are optional and come in this
   order. They are not written as [premises? args? attribute*] because, all
   starting with [COLON], the parser could not decide whether [premises] is
   absent when it sees one. Here, it decides on the token after [COLON]. *)
step_annotations:
  | ps=premises aa=then_attributes(args) { (ps, aa) }
  | aa=then_attributes(args) { ([], aa) }

(* [then_attributes(X)] parses an optional [X], which produces a list, followed
   by attributes. It returns [([], attrs)] when [X] is absent. *)
then_attributes(X):
  | attrs=attribute* { ([], attrs) }
  | x=X attrs=attribute* { (x, attrs) }

premises:
  | COLON PREMISES LEFTPAR ps=SYMBOL+ RIGHTPAR { ps }

args:
  | COLON ARGS LEFTPAR ts=term+ RIGHTPAR { ts }

context:
  | COLON ARGS LEFTPAR cs=context_assignment+ RIGHTPAR { cs }

context_assignment:
  | x=sorted_var { Var x }
  | LEFTPAR ASSIGN x=sorted_var t=term RIGHTPAR { Assign(x, t) }

sorted_var:
  | LEFTPAR x=SYMBOL s=term RIGHTPAR { (x, s) }

(* SMT-LIB attribute [:k] or [:k v]. *)
attribute:
  | COLON k=SYMBOL v=attribute_value? { (k, v) }

attribute_value:
  | s=SYMBOL { SSymbol s }
  | c=constant { SConst c }
  | LEFTPAR es=s_expr* RIGHTPAR { SList es }

s_expr:
  | s=SYMBOL { SSymbol s }
  | c=constant { SConst c }
  | COLON k=SYMBOL { SKeyword k }
  | LEFTPAR es=s_expr* RIGHTPAR { SList es }

constant:
  | n=NUMERAL { Numeral n }
  | n=NEGNUMERAL { Numeral n }
  | d=DECIMAL { Decimal d }
  | d=NEGDECIMAL { Decimal d }
  | r=RATIONAL { Rational r }
  | h=HEXADECIMAL { Hexadecimal h }
  | b=BINARY { Binary b }
  | s=STRING { String s }

term:
  | s=SYMBOL { Symbol s }
  | c=constant { Const c }
  | LEFTPAR f=SYMBOL ts=term+ RIGHTPAR { App(f, ts) }
  | LEFTPAR BANG t=term attrs=attribute+ RIGHTPAR { Annot(t, attrs) }
  | LEFTPAR FORALL b=bind RIGHTPAR { let (xs, t) = b in Forall(xs, t) }
  | LEFTPAR EXISTS b=bind RIGHTPAR { let (xs, t) = b in Exists(xs, t) }
  | LEFTPAR CHOICE b=bind RIGHTPAR
    { match b with
      | ([x], t) -> Choice(x, t)
      | _ -> fail $loc(b) "choice binds exactly one variable." }
  | LEFTPAR LET LEFTPAR bs=var_binding+ RIGHTPAR t=term RIGHTPAR
    { Let(bs, t) }

(* Variables and body of the binders forall, exists and choice. *)
bind:
  | LEFTPAR xs=sorted_var+ RIGHTPAR t=term { (xs, t) }

(* Binding [(x t)] of a let. *)
var_binding:
  | LEFTPAR x=SYMBOL t=term RIGHTPAR { (x, t) }