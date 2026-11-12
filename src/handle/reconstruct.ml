(** Reconstruction of the Alethe proofs returned by CVC5 for the why3 tactic.

    PLACEHOLDER: first architecture, to be reviewed and rewritten. The
    plumbing is written, the logical parts are stubs that raise
    [Unsupported], and the tactic then admits the goal as before.

    Pipeline ([replay]):
    + [extract]: cut the proof out of the prover output.
    + [parse]: Alethe commands ({!module:Parsing.AletheSyntax}).
    + [term]: Alethe term → lambdapi proposition, with the names recorded
      by [Why3_tactic.translate_goal].
    + [assume]: match each [assume] with a hypothesis of the goal, or with
      the negated goal, and build its proof in the reading ([hyp], [goal]).
    + [step]: one proof term per step, built from the proofs of its
      premises. The proof of the step [(cl)] is the proof of the goal.

    Reading, with answer [r] (here [r] := the goal; see AGENTS.md and
    tests/constructionism/alethe_rules.lp):
    - [(cl l₁ … lₙ)] is [(⟦l₁⟧ ⇒ r) ⇒ … ⇒ (⟦lₙ⟧ ⇒ r) ⇒ r];
    - [⟦not a⟧ = ⟦a⟧ ⇒ r], [⟦false⟧ = r], [T r a = (a ⇒ r) ⇒ r] is
      inserted after [⇒] and [∀].

    Excluded middle. The tactic never uses an [em] axiom. Where the replay
    needs excluded middle on a formula [a], it calls [dec], which creates
    a hole of type [π (a ∨ ¬ a)]. The holes become new goals: the user
    proves these decidability instances. Where it is needed:
    - [goal]: [π ⟦G⟧ → π G], at each [¬ a] and [a ⇒ b] of [G];
    - [hyp]: [π H → π (T r ⟦H⟧)], at each [¬ a] and [a ⇒ b] in negative
      position in [H];
    - steps whose rule has no intuitionistic lemma ([sko_*]).
    TODO: [∀] in negative position needs [(∀x. a) ∨ ∃x. ¬ a], not [dec]. *)

open Lplib
open Common open Error
open Core open Term
open Parsing
open Goal

(** Logging function for proof reconstruction. *)
let log = Logger.make 'f' "rcon" "proof reconstruction"
let log = log.pp

(** Raised when a proof cannot be replayed. The tactic then admits the
    goal. *)
exception Unsupported of string

let unsupported fmt = Format.kasprintf (fun s -> raise (Unsupported s)) fmt

(** [names] maps the SMT-LIB symbols of the current proof to lambdapi
    terms: the symbols of the task (set by [replay]) and the terms named by
    [(! t :named @p_k)] (added by [from_alethe]). FIXME: the task symbols
    are the names given to Why3, and its printer may change them ([succ']
    → [succqt], second [X] → [X1]). *)
let names : (string, term) Hashtbl.t = Hashtbl.create 17

type proof =  {
  term: term;
 (*assumes: term VarMap.t; *)
  env: Env.t;
  (** Commands bound so far: [(id, (x, type, Some proof))], the first
      command of the proof first. *)
}

(** [extract out] returns the commands of the Alethe proof printed in
    [out]: the lines between the line ["("] that follows ["unsat"] and the
    next line [")"]. *)
let extract : string -> string = fun out ->
  let rec skip = function
    | "unsat" :: "(" :: ls -> ls
    | _ :: ls -> skip ls
    | [] -> unsupported "no proof in the prover output"
  in
  let rec take acc = function
    | ")" :: _ -> String.concat "\n" (List.rev acc)
    | l :: ls -> take (l::acc) ls
    | [] -> unsupported "unterminated proof"
  in
  take [] (skip (List.map String.trim (String.split_on_char '\n' out)))

(** [parse s] parses the Alethe commands of [s]. *)
let parse : string -> AletheSyntax.command list = fun s ->
  let cmds = ref [] in
  try
    Stream.iter (fun c -> cmds := c.Pos.elt :: !cmds)
      (Parser.Alethe.parse_string "cvc5" s);
    List.rev !cmds
  with Fatal(_,msg,_) -> unsupported "parse error: %s" msg

(** [from_alethe cfg t] translates the Alethe formula or term [t] to
    lambdapi (no reading: [not] is [¬]). It records the [:named]
    annotations in [names]. *)
let rec from_alethe : Why3_tactic.config -> AletheSyntax.term -> term =
  fun c t ->
  let app s ts = add_args (mk_Symb s) (List.map (from_alethe c) ts) in
  match t with
  | Symbol "true" -> mk_Symb c.symb_top
  | Symbol "false" -> mk_Symb c.symb_bot
  | Symbol x | App(x, []) ->
      begin
        match Hashtbl.find_opt names x with
        | Some u -> u
        | None -> unsupported "unknown symbol %s" x
      end
  | App("not", ([_] as ts)) -> app c.symb_not ts
  | App("and", ([_;_] as ts)) -> app c.symb_and ts
  | App("or", ([_;_] as ts)) -> app c.symb_or ts
  | App("=>", ([_;_] as ts)) -> app c.symb_imp ts
  (* TODO: n-ary and/or/=>, [=] (⇔ on formulas, equality on terms). *)
  | App(f, ts) -> add_args (from_alethe c (Symbol f)) (List.map (from_alethe c) ts)
  | Annot(t, attrs) ->
      let u = from_alethe c t in
      let name = function
        | ("named", Some(AletheSyntax.SSymbol n)) ->
            Hashtbl.replace names n u
        | _ -> ()
      in
      List.iter name attrs; u
  | Forall _ | Exists _ -> unsupported "quantifier" (* TODO *)
  | Choice _ -> unsupported "choice"
  | Let _ -> unsupported "let"
  | Const _ -> unsupported "constant"

(** [trace cfg cmds] logs the commands [cmds] with their formulas translated
    to lambdapi, before any proof is built. *)
let trace : Why3_tactic.config -> AletheSyntax.command list -> unit = fun cfg ->
  let terms ppf = List.iter (Format.fprintf ppf " [%a]" Print.term) in
  let strings ppf = List.iter (Format.fprintf ppf " %s") in
  let command : AletheSyntax.command -> unit = function
    | Assume(id,t,_) -> log "assume %s: %a" id Print.term (from_alethe cfg t)
    | Step{id; clause; rule; premises; _} ->
        log "step %s: (cl%a) by %s%a" id terms (List.map (from_alethe cfg) clause)
          rule strings premises
    | Anchor(id,_,_) -> log "anchor %s" id
    | DefineFun(f,_,_,_) -> log "define-fun %s" f
  in
  List.iter (fun c -> try command c with Unsupported s -> log "? %s" s)


(** [append (id,t) p body] binds the proof [t] of the command [id]: it
    returns [let id ≔ t in u], where [u] is the term of [body p'] and [p']
    is [p] with the new variable [id] added to its environment. The rest of
    the proof is built by [body], so that it can refer to [id] through
    [p'.env]. The type of [id] is a placeholder, to be inferred when the
    term is refined. *)
let append : string * term -> proof -> (proof -> proof) -> proof =
  fun (id,t) p body ->
    let x = new_var id in
    let a = mk_Plac true in
    let p' = body {p with env = (id, (x, a, Some t)) :: p.env} in
    {p' with term = mk_LLet(a, t, bind_var x p'.term)}

(** [match_step cfg cmd p body] binds the proof of the command [cmd], and
    builds the rest of the proof with [body]. *)
let match_step :
  Why3_tactic.config -> AletheSyntax.command -> proof -> (proof -> proof)
  -> proof =
  fun cfg cmd p body ->
    match cmd with
    | Assume(id,t,_) ->
        let tterm = from_alethe cfg t in
        append (id, tterm) p body
    | Step{id=_; clause=_cl; rule=_; premises=_; args=_; _} -> (* TODO *)
        body p
    | Anchor(id,_,_) -> unsupported "anchor %s" id (* TODO: subproof, bind *)
    | DefineFun(f,_,_,_) -> unsupported "define-fun %s" f

(** [walk cfg cmds p] binds the commands [cmds] in order around [p.term].
    Each command sees the previous ones in the environment. *)
let rec walk :
  Why3_tactic.config -> AletheSyntax.command list -> proof -> proof =
  fun cfg cmds p ->
    match cmds with
    | cmd :: cmds -> match_step cfg cmd p (walk cfg cmds)
    | [] -> p

(** [pp_lets ppf t] prints the term [t] with the name of every
    let-bound variable. [Print.term] prints [_] for a variable that does
    not occur in the body of its let. *)
let rec pp_lets : Format.formatter -> term -> unit = fun ppf t ->
  match unfold t with
  | LLet(_,u,b) ->
      let x,v = unbind b in
      Format.fprintf ppf "let %s ≔ %a in@ %a" (base_name x) Print.term u
        pp_lets v
  | t -> Print.term ppf t

let replay :
  Sig_state.t -> Pos.popt -> goal_typ -> string * (string * term) list
  -> problem -> term =
  fun ss pos gt (out,task_names) _p ->
  let cfg = Why3_tactic.get_config ss pos in
  let g =
    match get_args gt.goal_type with
    | Symb s, [g] when s == cfg.symb_P -> g
    | _ -> unsupported "the goal is not a proposition"
  in
  ignore g;
  Hashtbl.reset names;
  List.iter (fun (n,t) -> Hashtbl.replace names n t) task_names;
  let cmds = parse (extract out) in
  if Logger.log_enabled() then trace cfg cmds;
  (* The environment starts with the hypotheses of the goal. *)
  let result = walk cfg cmds {term=mk_Plac false; env=gt.goal_hyps} in
  if Logger.log_enabled() then log "proof term: @[<v>%a@]" pp_lets result.term;
  result.term
