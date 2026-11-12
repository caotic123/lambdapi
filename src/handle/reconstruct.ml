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

(** Builtins of the library that reconstructed proofs depend on
    (tests/smtlib/Core.lp): the disjunction [disj] of a clause, and the
    judgement [π̇] "the clause holds". *)
let _ =
  List.iter (fun n -> Builtin.register n Builtin.no_check)
    ["smt_disj"; "smt_clause"; "smt_o"; "smt_nil"; "smt_cons"; "smt_or_neg"; "smt_implies";
     "smt_em_top"; "smt_em_bot"; "smt_em_not"; "smt_em_and"; "smt_em_or";
     "smt_em_imp"]

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

(** Symbols of the library that reconstructed proofs depend on
    (tests/smtlib/Core.lp), and of the natural numbers. *)
type lib =
  { o : sym (** Set of propositions. *)
  ; nil : sym (** Empty list. *)
  ; cons : sym (** List cons. *)
  ; disj : sym (** Disjunction of a list of propositions. *)
  ; or_neg : sym (** Lemma of the rule or_neg. *)
  ; implies : sym (** Lemma of the rule implies. *)
  ; em_top : sym (** Excluded middle on [⊤]. *)
  ; em_bot : sym (** Excluded middle on [⊥]. *)
  ; em_not : sym (** Excluded middle on [¬ p], from the one on [p]. *)
  ; em_and : sym (** The same for [p ∧ q]. *)
  ; em_or : sym (** The same for [p ∨ q]. *)
  ; em_imp : sym (** The same for [p ⇒ q]. *)
  ; zero : sym
  ; succ : sym }

(** Data of the goal being replayed, set by [replay]. *)
type goal =
  { lib : lib
  ; problem : problem (** Receives the excluded middle holes. *)
  ; ctxt : ctxt (** Hypotheses of the goal. *) }

let goal : goal option ref = ref None

let get_goal() =
  match !goal with Some g -> g | None -> assert false

(** [get_lib ss pos] builds the library configuration using [ss]. *)
let get_lib : Sig_state.t -> Pos.popt -> lib = fun ss pos ->
  let builtin n =
    try Builtin.get ss pos [] n
    with Fatal _ ->
      unsupported "builtin %s not found (require tests.smtlib.Core)" n
  in
  { o = builtin "smt_o"; nil = builtin "smt_nil"; cons = builtin "smt_cons"
  ; disj = builtin "smt_disj"; or_neg = builtin "smt_or_neg"
  ; implies = builtin "smt_implies"
  ; em_top = builtin "smt_em_top"; em_bot = builtin "smt_em_bot"
  ; em_not = builtin "smt_em_not"; em_and = builtin "smt_em_and"
  ; em_or = builtin "smt_em_or"; em_imp = builtin "smt_em_imp"
  ; zero = builtin "nat_zero"; succ = builtin "nat_succ" }

(** [list_of ts] returns the list [t₁ ⸬ … ⸬ tₙ ⸬ □] of propositions. *)
let list_of : term list -> term = fun ts ->
  let l = (get_goal()).lib in
  let o = mk_Symb l.o in
  List.fold_right (fun t u -> add_args (mk_Symb l.cons) [o;t;u]) ts
    (mk_Appl(mk_Symb l.nil, o))

(** [elements t] returns [[t₁;…;tₙ]] if [t] is [t₁ ⸬ … ⸬ tₙ ⸬ □]. *)
let rec elements : term -> term list = fun t ->
  let l = (get_goal()).lib in
  match get_args t with
  | Symb s, [_;x;u] when s == l.cons -> x :: elements u
  | Symb s, [_] when s == l.nil -> []
  | _ -> unsupported "not a list"

(** [nat_of n] returns the natural number [n]. *)
let rec nat_of : int -> term = fun n ->
  let l = (get_goal()).lib in
  if n <= 0 then mk_Symb l.zero
  else mk_Appl(mk_Symb l.succ, nat_of (n-1))

type proof =  {
  term: term;
 (*assumes: term VarMap.t; *)
  env: Env.t;
  (** Commands bound so far: [(id, (x, type, Some proof))], the first
      command of the proof first. *)
  em: (term * term) list;
  (** Queue of the excluded middle instances the proof needs, to ask the
      user for at the end: [(a, h)] with [a] an atom and [h] a hole of type
      [π (a ∨ ¬ a)]. The last instance queued is first. *)
}

(** [ask_em cfg p a] returns a proof of [π (a ∨ ¬ a)] and the updated
    proof. The proof is built from the excluded middle instances for the
    atoms of [a] with the lemmas [em_and], [em_or], … Only atoms are queued:
    for an atom, the proof is the hole already queued for a convertible
    atom, or a new hole added to the queue. *)
let rec ask_em : Why3_tactic.config -> proof -> term -> term * proof =
  fun c p a ->
  let g = get_goal() in
  let l = g.lib in
  let binary lem a b =
    let ea, p = ask_em c p a in
    let eb, p = ask_em c p b in
    add_args (mk_Symb lem) [a;b;ea;eb], p
  in
  match get_args a with
  | Symb s, [] when s == c.symb_top -> mk_Symb l.em_top, p
  | Symb s, [] when s == c.symb_bot -> mk_Symb l.em_bot, p
  | Symb s, [a] when s == c.symb_not ->
      let ea, p = ask_em c p a in add_args (mk_Symb l.em_not) [a;ea], p
  | Symb s, [a;b] when s == c.symb_and -> binary l.em_and a b
  | Symb s, [a;b] when s == c.symb_or -> binary l.em_or a b
  | Symb s, [a;b] when s == c.symb_imp -> binary l.em_imp a b
  (* a ⇔ b is (a ⇒ b) ∧ (b ⇒ a) *)
  | Symb s, [a;b] when s == c.symb_eqv ->
      let imp a b = add_args (mk_Symb c.symb_imp) [a;b] in
      binary l.em_and (imp a b) (imp b a)
  (* disj (a₁ ⸬ … ⸬ aₙ ⸬ □) is a₁ ∨ … ∨ aₙ ∨ ⊥ *)
  | Symb s, [as_] when s == l.disj ->
      let disj ts = mk_Appl(mk_Symb l.disj, list_of ts) in
      let rec em p = function
        | [] -> mk_Symb l.em_bot, p
        | a::ts ->
            let ea, p = ask_em c p a in
            let ets, p = em p ts in
            add_args (mk_Symb l.em_or) [a; disj ts; ea; ets], p
      in
      em p (elements as_)
  | _ -> (* atom *)
      match List.assoc_eq_opt (Eval.eq_modulo g.ctxt) a p.em with
      | Some h -> h, p
      | None ->
          let not_a = mk_Appl(mk_Symb c.symb_not, a) in
          let ty =
            mk_Appl(mk_Symb c.symb_P,
                    add_args (mk_Symb c.symb_or) [a; not_a]) in
          let h = LibMeta.make g.problem g.ctxt ty in
          h, {p with em = (a,h)::p.em}

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
  (* [(or t₁ … tₙ)] is the disjunction of the clause [t₁ ⸬ … ⸬ tₙ ⸬ □]. *)
  | App("or", ts) ->
      let l = (get_goal()).lib in
      mk_Appl(mk_Symb l.disj, list_of (List.map (from_alethe c) ts))
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
    returns [let id : a ≔ t in u], where [a] is the type inferred for [t]
    in the environment [p.env], [u] is the term of [body p'] and [p'] is
    [p] with the new variable [id] added to its environment. The rest of
    the proof is built by [body], so that it can refer to [id] through
    [p'.env].
    @raise Unsupported if [t] is not typable. *)
let append : string * term -> proof -> (proof -> proof) -> proof =
  fun (id,t) p body ->
    let g = get_goal() in
    let t, a =
      match Infer.infer_noexn g.problem (Env.to_ctxt p.env) t with
      | Some ta when Unif.solve_noexn ~print:false g.problem -> ta
      | _ -> unsupported "%s: ill-typed term %a" id Print.term t
    in
    let x = new_var id in
    let p' = body {p with env = (id, (x, a, Some t)) :: p.env} in
    {p' with term = mk_LLet(a, t, bind_var x p'.term)}
  

let compute_step = fun cfg id clause rule premises args body p ->
  match rule with
    | "or_neg" -> 
      let d = match clause with
         | [d; _] -> d
         | _ -> unsupported "step %s: no cl clause" id
      in
      let k = match (args : AletheSyntax.term list) with
         | [Const(Numeral k)]-> k
         | _ -> unsupported "step %s: no specified number in args" id
      in
      let l = (get_goal()).lib in
      let phis =
        match get_args (from_alethe cfg d) with
        | Symb s, [phis] when s == l.disj -> phis
        | _ -> unsupported "step %s: no disjunction" id
      and k = int_of_string k in
      let phi_k =
        try List.nth (elements phis) k
        with Failure _ | Invalid_argument _ ->
          unsupported "step %s: no literal %d" id k
      in
      let em, p = ask_em cfg p phi_k in
      let prf = add_args (mk_Symb l.or_neg) [phis; nat_of k; em] in
      append (id, prf) p body
    (* (cl (not φ₁) φ₂) from the premise φ₁ ⇒ φ₂ *)
    | "implies" ->
      let l = (get_goal()).lib in
      let phi1, phi2 =
        match List.map (from_alethe cfg) clause with
        | [n; phi2] ->
            begin
              match get_args n with
              | Symb s, [phi1] when s == cfg.symb_not -> phi1, phi2
              | _ -> unsupported "step %s: no negation" id
            end
        | _ -> unsupported "step %s: no cl clause" id
      in
      let h =
        match premises with
        | [h] ->
            begin
              match List.assoc_opt h p.env with
              | Some(x,_,_) -> mk_Vari x
              | None -> unsupported "step %s: unknown premise %s" id h
            end
        | _ -> unsupported "step %s: one premise expected" id
      in
      let em, p = ask_em cfg p phi1 in
      let prf = add_args (mk_Symb l.implies) [phi1; phi2; em; h] in
      append (id, prf) p body
    | _ -> body p


(** [match_step cfg cmd p body] binds the proof of the command [cmd], and
    builds the rest of the proof with [body]. *)
let match_step :
  Why3_tactic.config -> AletheSyntax.command -> proof -> (proof -> proof)
  -> proof =
  fun cfg cmd p body ->
    match cmd with
    | Assume(id,t,_) ->
        let tterm = from_alethe cfg t in
        (* The proof of an assumption is the hypothesis of the goal that
           states it. FIXME: without one (the negated goal, a hypothesis
           changed by Why3), the formula itself is bound. *)
        let pi_t = mk_Appl(mk_Symb cfg.symb_P, tterm) in
        let ctxt = Env.to_ctxt p.env in
        let is_hyp (_,(_,a,_)) = Eval.eq_modulo ctxt a pi_t in
        let tterm =
          match List.find_opt is_hyp p.env with
          | Some(_,(x,_,_)) -> mk_Vari x
          | None -> tterm
        in
        append (id, tterm) p body
    (* (cl (or φ₁ … φₙ) (not φₖ)) :args (k) *)
    | Step{id; clause; rule; premises; args; _} ->
        compute_step cfg id clause rule premises args body p
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
  | LLet(a,u,b) ->
      let x,v = unbind b in
      Format.fprintf ppf "let %s : %a@   ≔ %a in@ %a" (base_name x)
        Print.term a Print.term u pp_lets v
  | t -> Print.term ppf t

(** [replay ss pos gt (out,names) p] returns the term built from the
    prover output [out] for the goal [gt], where [names] maps the SMT-LIB
    symbols to lambdapi terms, and the queue of the excluded middle
    instances [(a, h)] it uses, in the order they were needed: [h] is a
    hole of type [π (a ∨ ¬ a)] added to [p].
    @raise Unsupported if the proof cannot be replayed. *)
let replay :
  Sig_state.t -> Pos.popt -> goal_typ -> string * (string * term) list
  -> problem -> term * (term * term) list =
  fun ss pos gt (out,task_names) problem ->
  let cfg = Why3_tactic.get_config ss pos in
  let g =
    match get_args gt.goal_type with
    | Symb s, [g] when s == cfg.symb_P -> g
    | _ -> unsupported "the goal is not a proposition"
  in
  ignore g;
  goal := Some {lib = get_lib ss pos; problem;
                ctxt = Env.to_ctxt gt.goal_hyps};
  Hashtbl.reset names;
  List.iter (fun (n,t) -> Hashtbl.replace names n t) task_names;
  let cmds = parse (extract out) in
  if Logger.log_enabled() then trace cfg cmds;
  (* The environment starts with the hypotheses of the goal. *)
  let result =
    walk cfg cmds {term=mk_Plac false; env=gt.goal_hyps; em=[]} in
  let em = List.rev result.em in
  if Logger.log_enabled() then
    begin
      log "proof term: @[<v>%a@]" pp_lets result.term;
      log "excluded middle needed for: @[<v>%a@]"
        (fun ppf -> List.iter (fun (a,_) ->
                        Format.fprintf ppf "%a@ " Print.term a)) em
    end;
  result.term, em
