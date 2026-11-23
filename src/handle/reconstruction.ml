(** Proof reconstruction through Carcara (experimental).

    When the why3 tactic gets an Alethe proof from CVC5 (see
    "--experimental-smt-proofs"), the proof and the SMT-LIB problem that Why3
    sent to CVC5 are handed to the Lambdapi backend of Carcara ("carcara
    translate lambdapi", from the fork NotBad4U/carcara, branch
    lambdapi-refactor). The Lambdapi file it produces is parsed, and its
    syntax tree is returned. *)

open Lplib
open Common
open Error
open Core

let log = Logger.make 'h' "carc" "Carcara reconstruction"
let log = log.pp
let command : string Stdlib.ref = Stdlib.ref "carcara"
let options = ["--expand-let-bindings"; "--allow-int-real-subtyping"]

(** [handle ss cmd] handles the command [cmd] in the state [ss], as in a
    file. It is [Command.handle], which this module cannot depend on: it is
    set by [Compile]. *)
let handle : (Sig_state.t -> Parsing.Syntax.p_command -> Sig_state.t)
    Stdlib.ref =
  Stdlib.ref (fun _ _ -> assert false)

(** The goal of a why3 call, after the introductions of the tactic. *)
type goal =
  { hyps : Env.env
  ; target : Term.term
  ; l2y : Why3_tactic.l2y
  ; why3_hyps : (string * Why3.Term.term) list
    (** In the order of the task: the N-th one is the Alethe assumption
        [aN]. *)
}

(** [names goal] maps the names that Carcara's translation declares to the
    terms of [goal] they stand for: the Why3 names of the symbols and
    variables of the goal (Carcara keeps the SMT-LIB names, which are the
    Why3 ones), and ["aN"] for the N-th hypothesis sent to the prover. *)
let names : goal -> Term.term Extra.StrMap.t = fun goal ->
  let open Extra in
  let ts_name ts = ts.Why3.Ty.ts_name.id_string in
  let ls_name ls = ls.Why3.Term.ls_name.id_string in
  let add f l m = List.fold_left (fun m x -> let n, t = f x in StrMap.add n t m) m l in
  let m = goal.l2y in
  StrMap.empty
  |> add (fun (s, ts) -> ts_name ts, Term.mk_Symb s) m.s2ts
  |> add (fun (t, ts) -> ts_name ts, t) m.t2ts
  |> add (fun (s, (ls, _)) -> ls_name ls, Term.mk_Symb s) m.s2ls
  |> add (fun (x, (ls, _)) -> ls_name ls, Term.mk_Vari x) m.v2ls
  |> add (fun (t, ls) -> ls_name ls, t) m.t2ls
  |> add (fun (i, (name, _)) ->
          let x, _, _ = List.assoc name goal.hyps in
          "a" ^ string_of_int i, Term.mk_Vari x)
       (List.mapi (fun i h -> i, h) goal.why3_hyps)

(** Lifting of Carcara's commands. The symbols that Carcara declares for
    the terms of the goal (the keys of [names]) cannot be declared: the goal
    variables are not symbols. Their declarations are removed, and they
    become parameters of every symbol declared after them. A reference to a
    lifted symbol [s] becomes [s x₁ … xₖ], where [x₁ … xₖ] are the
    parameters that [s] got. It is done in one pass over the commands. *)
module Lift = struct
  open Parsing.Syntax
  open Extra

  (** The parameters so far, with their types (already lifted). *)
  type params = (p_ident * p_term) list

  (** The names of the parameters that each lifted symbol got, in order. *)
  type arity = string list StrMap.t

  (** [app_term arity t] replaces in [t] every symbol [s] of [arity] by [s]
      applied to its parameters. Binders are not taken into account. *)
  let rec app_term : arity -> p_term -> p_term = fun arity t ->
    (* [app_vars t xs] is the term [t x₁ … xₖ]. *)
    let rec app_vars : p_term -> string list -> p_term = fun t xs ->
      match xs with
      | [] -> t
      | x :: xs ->
          let var = {t with elt = P_Iden ({t with elt = ([], x)}, false)} in
          app_vars {t with elt = P_Appl (t, var)} xs
    in
    match t.elt with
    | P_Iden ({elt = ([], s); _}, _) when StrMap.mem s arity ->
        app_vars t (StrMap.find s arity)
    | P_Type | P_Iden _ | P_Wild | P_Patt _ | P_NLit _ | P_SLit _ -> t
    | P_Meta (m, ts) -> {t with elt = P_Meta (m, Array.map (app_term arity) ts)}
    | P_Appl (u, v) -> {t with elt = P_Appl (app_term arity u, app_term arity v)}
    | P_Arro (u, v) -> {t with elt = P_Arro (app_term arity u, app_term arity v)}
    | P_Wrap u -> {t with elt = P_Wrap (app_term arity u)}
    | P_Expl u -> {t with elt = P_Expl (app_term arity u)}
    | P_Abst (ps, u) ->
        {t with elt = P_Abst (app_params arity ps, app_term arity u)}
    | P_Prod (ps, u) ->
        {t with elt = P_Prod (app_params arity ps, app_term arity u)}
    | P_LLet (y, ps, a, u, v) ->
        {t with elt =
           P_LLet (y, app_params arity ps, app_term_opt arity a,
                   app_term arity u, app_term arity v)}

  (** [app_term_opt arity t] is [app_term] on an optional term. *)
  and app_term_opt : arity -> p_term option -> p_term option = fun arity t ->
    match t with
    | None -> None
    | Some t -> Some (app_term arity t)

  (** [app_params arity ps] is [app_term] on the types of the binder or
      symbol arguments [ps]. *)
  and app_params : arity -> p_params list -> p_params list = fun arity ps ->
    match ps with
    | [] -> []
    | (ids, a, impl) :: ps ->
        (ids, app_term_opt arity a, impl) :: app_params arity ps

  (** [app_tactic arity t] is [app_term] on the terms of the tactic [t]. *)
  let rec app_tactic : arity -> p_tactic -> p_tactic = fun arity t ->
    match t.elt with
    | P_tac_and (t1, t2) ->
        {t with elt = P_tac_and (app_tactic arity t1, app_tactic arity t2)}
    | P_tac_orelse (t1, t2) ->
        {t with elt = P_tac_orelse (app_tactic arity t1, app_tactic arity t2)}
    | P_tac_repeat u -> {t with elt = P_tac_repeat (app_tactic arity u)}
    | P_tac_try u -> {t with elt = P_tac_try (app_tactic arity u)}
    | P_tac_all_hyps u -> {t with elt = P_tac_all_hyps (app_term arity u)}
    | P_tac_first_hyp u -> {t with elt = P_tac_first_hyp (app_term arity u)}
    | P_tac_apply u -> {t with elt = P_tac_apply (app_term arity u)}
    | P_tac_change u -> {t with elt = P_tac_change (app_term arity u)}
    | P_tac_eval u -> {t with elt = P_tac_eval (app_term arity u)}
    | P_tac_refine u -> {t with elt = P_tac_refine (app_term arity u)}
    | P_tac_have (y, u) -> {t with elt = P_tac_have (y, app_term arity u)}
    | P_tac_set (y, u) -> {t with elt = P_tac_set (y, app_term arity u)}
    | P_tac_rewrite (b, p, u) ->
        {t with elt = P_tac_rewrite (b, p, app_term arity u)}
    | _ -> t

  (** [app_proof arity p] is [app_term] on the terms of the proof [p], a
      list of subproofs. A subproof is a list of tactics, each with its own
      subproofs. *)
  let app_proof : arity -> p_proof -> p_proof = fun arity p ->
    let rec proof : p_proof -> p_proof = fun p ->
      match p with
      | [] -> []
      | sp :: p -> subproof sp :: proof p
    and subproof : p_subproof -> p_subproof = fun sp ->
      match sp with
      | [] -> []
      | Tactic (t, p) :: sp ->
          Tactic (app_tactic arity t, proof p) :: subproof sp
    in
    proof p

  (** [intro pos params p] is the proof [p] starting with the tactic
      [assume x₁ … xₖ], at the position [pos]: a proof script does not
      introduce the arguments of its symbol. *)
  let intro : Pos.popt -> params -> p_proof -> p_proof = fun pos params p ->
    let rec idents : params -> p_ident option list = fun params ->
      match params with
      | [] -> []
      | (x, _) :: params -> Some x :: idents params
    in
    match params with
    | [] -> p
    | _ ->
        let assume = Tactic (Pos.make pos (P_tac_assume (idents params)), []) in
        match p with
        | [] -> [[assume]]
        | sp :: p -> (assume :: sp) :: p

  (** [lift_symbol arity params ps] adds [params] in front of the arguments
      of the symbol [ps], introduces them at the start of its proof, and
      applies the symbols of [arity] to their parameters. *)
  let lift_symbol : arity -> params -> p_symbol -> p_symbol =
    fun arity params ps ->
    let rec args : params -> p_params list = fun params ->
      match params with
      | [] -> []
      | (x, a) :: params -> ([Some x], Some a, false) :: args params
    in
    let proof =
      match ps.p_sym_prf with
      | None -> None
      | Some (p, e) ->
          Some (intro ps.p_sym_nam.pos params (app_proof arity p), e)
    in
    { ps with
      p_sym_arg = args params @ app_params arity ps.p_sym_arg
    ; p_sym_typ = app_term_opt arity ps.p_sym_typ
    ; p_sym_trm = app_term_opt arity ps.p_sym_trm
    ; p_sym_prf = proof }

  (** [lift_commands names rev_params arity cmds] lifts the commands [cmds],
      where [rev_params] are the parameters so far, last one first, and
      [arity] the symbols lifted so far. *)
  let rec lift_commands :
    Term.term StrMap.t -> params -> arity -> p_command list -> p_command list
    = fun names rev_params arity cmds ->
    let rec names_of : params -> string list = fun params ->
      match params with
      | [] -> []
      | (x, _) :: params -> x.elt :: names_of params
    in
    let is_global : string -> bool = fun x ->
      match StrMap.find_opt x names with
      | Some (Term.Symb _) -> true
      | _ -> false
    in
    match cmds with
    | [] -> []
    | {elt = P_symbol {p_sym_nam = x; _}; _} :: cmds when is_global x.elt ->
        (* A symbol of the goal: not declared and not lifted, the later
           commands refer to the symbol itself. This assumes that the file
           is in the encoding of Carcara's library (the Stdlib), and that
           the symbol is in scope under this name. *)
        lift_commands names rev_params arity cmds
    | {elt = P_symbol {p_sym_nam = x; p_sym_typ = Some a; _}; _} :: cmds
      when StrMap.mem x.elt names ->
        (* A variable of the goal: not declared, a parameter from now on. Its
           type may use the symbols lifted so far. *)
        lift_commands names ((x, app_term arity a) :: rev_params) arity cmds
    | ({elt = P_symbol ps; _} as cmd) :: cmds ->
        let params = List.rev rev_params in
        let cmd = {cmd with elt = P_symbol (lift_symbol arity params ps)} in
        (* [ps] is added to [arity] after it is lifted: it does not refer
           to itself. *)
        let arity = StrMap.add ps.p_sym_nam.elt (names_of params) arity in
        cmd :: lift_commands names rev_params arity cmds
    | cmd :: cmds -> cmd :: lift_commands names rev_params arity cmds

  (** [lift names cmds] lifts the symbols of [cmds] whose name is in
      [names]. *)
  let lift : Term.term StrMap.t -> p_command list -> p_command list =
    fun names cmds -> lift_commands names [] StrMap.empty cmds
end

(** [handle_onfly_commands names cmds ss] handles the commands [cmds] in
    the state [ss]. A symbol whose name is in [names] (see [names]) stands
    for a term of the goal: it is skipped instead of declared. *)
let rec handle_onfly_commands :
  Term.term Extra.StrMap.t -> Parsing.Syntax.p_commands -> Sig_state.t
  -> Sig_state.t =
  fun names cmds ss ->
    match Stream.next cmds with
    | exception Stream.Failure -> ss
    | {elt=P_symbol ps; _} when Extra.StrMap.mem ps.p_sym_nam.elt names ->
        handle_onfly_commands names cmds ss
    | {elt=P_symbol ps; pos} when Sign.mem ss.signature ps.p_sym_nam.elt ->
        (* A symbol of Carcara (e.g. a step [t0] or a definition [p_1])
           with the name of a symbol of the current module: it does not
           stand for a term of the goal, and cannot be declared. *)
        fatal pos "Lambdapi's symbol %s clashes with a symbol of the module."
          ps.p_sym_nam.elt
    | {elt=P_require _ | P_symbol _; _} as cmd ->
        (* Compile the command (for a definition, its right side) and add
           it to [ss]. *)
        handle_onfly_commands names cmds (Stdlib.(!handle) ss cmd)
    | {pos; _} ->
        fatal pos "Command not produced by Carcara's Lambdapi backend."

(** [inject names ss cmds] handles the commands [cmds] one after the other,
    starting in the state [ss], and returns the final state. If a command
    fails, what was added before it is undone, and the result is [None],
    with a warning. *)
let inject :
  Term.term Extra.StrMap.t -> Sig_state.t -> Parsing.Syntax.p_commands
  -> Sig_state.t option =
  fun names ss cmds ->
  let time = Timed.Time.save () in
  try
    let rec to_list cmds =
      match Stream.next cmds with
      | cmd -> cmd :: to_list cmds
      | exception Stream.Failure -> []
    in
    let cmds = Lift.lift names (to_list cmds) in
    if Logger.log_enabled() then
      List.iter (log "lifted: %a" Parsing.Pretty.command) cmds;
    let cmds = Stream.of_list cmds in
    let ss = handle_onfly_commands names cmds ss in
    Console.out 1 (Color.blu "checked with sucess");
    Some ss
  with Fatal(_, msg, _) ->
    Timed.Time.restore time;
    Console.out 1 "Carcara: the translation cannot be checked: %s"
      msg;
    None

(** [output ss pos ~goal ~problem ~output] translates with Carcara the Alethe proof
    printed by the prover in [output] for the SMT-LIB [problem], and returns
    the stream of the commands of the Lambdapi file obtained. The
    translation is first tried strictly, then with "--admit-unsupported".
    The files are kept in a fresh temporary directory, which is logged. The
    result is [None], with a warning, if Carcara gives no translation or if
    its file cannot be opened. The stream is parsed lazily: a syntax error
    is raised when the stream is consumed. *)
let output :
  Sig_state.t -> Pos.popt -> goal:goal -> problem:string -> output:string
  -> Parsing.Syntax.p_commands option =
  fun ss pos ~goal ~problem ~output ->
  begin
    (* [Print.ctxt] prints the types only with [print_domains]. *)
    let hyp ppf (n, (_, a, _)) = Format.fprintf ppf "%s : %a" n Print.term a in
    log "goal: %a ⊢ %a" (List.pp hyp ", ") (List.rev goal.hyps)
      Print.term goal.target;
    let name ppf (n, t) = Format.fprintf ppf "%s ↦ %a" n Print.term t in
    log "names: %a" (List.pp name ", ")
      (Extra.StrMap.bindings (names goal))
  end;
  (* The files of this call, in a fresh temporary directory. *)
  let dir = Filename.temp_file "lambdapi_carcara_" "" in
  Sys.remove dir; Sys.mkdir dir 0o700;
  let file f = Filename.concat dir f in
  let write f s = Out_channel.with_open_bin (file f) (fun oc -> output_string oc s) in
  let read f =
    try In_channel.with_open_bin (file f) In_channel.input_all
    with Sys_error _ -> ""
  in
  write "problem.smt2" problem;
  (* Carcara reads the output of the prover from its answer on: the output
     may start with other messages, e.g. warnings of the dynamic linker. *)
  let rec from_unsat = function
    | l :: ls when String.trim l <> "unsat" -> from_unsat ls
    | ls -> ls
  in
  write "proof.alethe"
    (match from_unsat (String.split_on_char '\n' output) with
     | [] -> output
     | ls -> String.concat "\n" ls);
  (* [translate extra] runs Carcara with the options [extra], writing the
     translation in proof.lp and its messages in carcara.err. *)
  let translate extra =
    let args =
      ["translate"; "lambdapi"; file "proof.alethe"; file "problem.smt2"]
      @ options @ extra
    in
    let cmd =
      Filename.quote_command !command args
        ~stdout:(file "proof.lp") ~stderr:(file "carcara.err")
    in
    if Logger.log_enabled() then log "%s" cmd;
    Sys.command cmd = 0
  in
  (* The first line of the messages of the last run of Carcara, if any. *)
  let carcara_error () =
    List.find_opt (fun l -> l <> "")
      (List.map String.trim (String.split_on_char '\n' (read "carcara.err")))
  in
  let parse mode =
    if Logger.log_enabled() then
      log "%a translated (%s) in %s" Pos.pp pos mode dir;
    try 
      let ast = (Parsing.Parser.parse_file (file "proof.lp")) in
      ignore (inject (names goal) ss ast);
      Some(ast)
    with Fatal(_, msg, _) ->
      wrn pos "Carcara: the translation does not parse: %s" msg; None
  in
  let no_message = Option.value ~default:"no error message" in
  if translate [] then parse "strict"
  else
    let reason = carcara_error () in
    if translate ["--admit-unsupported"] then
      parse ("--admit-unsupported, strict failed: " ^ no_message reason)
    else
      let msg =
        match carcara_error () with Some m -> m | None -> no_message reason
      in
      wrn pos "Carcara: no translation (files in %s): %s" dir msg; None
