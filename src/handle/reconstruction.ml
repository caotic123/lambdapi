(** Proof reconstruction through Carcara (experimental).

    When the why3 tactic gets an Alethe proof from CVC5 (see
    "--experimental-smt-proofs"), the proof and the SMT-LIB problem that Why3
    sent to CVC5 are handed to the Lambdapi backend of Carcara ("carcara
    translate lambdapi", from the fork NotBad4U/carcara, branch
    lambdapi-refactor). The Lambdapi file it produces is loaded as a module
    in the current process, which type-checks it, and the current signature
    depends on it. That module is written in the encoding of Carcara's own
    library (the package [alethe], over the Lambdapi Stdlib), not in the one
    of the goal: what relates the two is left as holes by the tactic. *)

open Common
open Error

let log = Logger.make 'h' "carc" "Carcara reconstruction"
let log = log.pp

(** {1 Running Carcara and Lambdapi} *)

(** Command running Carcara. Set by "--carcara". *)
let command : string Stdlib.ref = Stdlib.ref "carcara"

(** Options of "carcara translate lambdapi": the parser flags that the
    proofs of CVC5 need. *)
let options = ["--expand-let-bindings"; "--allow-int-real-subtyping"]

let write : string -> string -> unit = fun file s ->
  Out_channel.with_open_bin file (fun oc -> output_string oc s)

let read : string -> string = fun file ->
  try In_channel.with_open_bin file In_channel.input_all
  with Sys_error _ -> ""

(** [translate dir extra] translates with Carcara, run with the options
    [extra], the Alethe proof [dir/proof.alethe] of the SMT-LIB problem
    [dir/problem.smt2] into the Lambdapi file [dir/proof.lp]. The messages
    of Carcara are kept in [dir/carcara.err]. It tells whether Carcara
    succeeded. *)
let translate : string -> string list -> bool = fun dir extra ->
  let file f = Filename.concat dir f in
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

(** {1 The translation as a Lambdapi AST} *)

open Pos
open Parsing
open Syntax

(** The [symbol] declarations of a translation, sorted by role, in the order
    of the file. *)
type translation =
  { commands : p_command list (** All the commands of the file. *)
  ; constants : p_symbol list
    (** [symbol x : T;] where [T] is not a proof type: the sorts and the
        function symbols of the problem. *)
  ; definitions : p_symbol list
    (** [symbol p_N ≔ t;]: the names of shared closed subterms. *)
  ; premises : p_symbol list
    (** [symbol aN : π̇ (A ⸬ □);]: the assertions of the problem, which are
        postulated. *)
  ; lemmas : p_symbol list
    (** [opaque symbol tN … ≔ begin … end;]: the steps of the proof, the
        theorem included. *)
  ; theorem : p_symbol option
    (** The last lemma: Carcara ends the file with the theorem that the
        proof establishes (see goal.rs in Carcara). *) }

(** [head t] is the identifier at the head of [t], if any. *)
let rec head : p_term -> string option = fun t ->
  match t.elt with
  | P_Wrap t | P_Appl(t,_) -> head t
  | P_Iden({elt=(_,s);_},_) -> Some s
  | _ -> None

(** [is_proof_type t] tells whether [t] is a proof type of Carcara's
    library: [π̇ l] (the clause [l] holds) or [π a] (the formula [a]
    holds). *)
let is_proof_type : p_term -> bool = fun t ->
  match head t with Some ("π̇" | "π") -> true | _ -> false

(** Role of a symbol declaration in a translation. *)
type role = Constant | Definition | Premise | Lemma

(** [role s] is the role of the symbol declaration [s], given by whether it
    is opaque, whether it has a definition, and whether its type is a proof
    type. *)
let role : p_symbol -> role = fun s ->
  let opaque = List.exists is_opaq s.p_sym_mod in
  let proof_type = Option.map is_proof_type s.p_sym_typ in
  match opaque, s.p_sym_trm, proof_type with
  | true , _     , _                   -> Lemma
  | false, Some _, _                   -> Definition
  | false, None  , Some true           -> Premise
  | false, None  , (Some false | None) -> Constant

(** [commands cs] is the list of the commands of the stream [cs]. *)
let rec commands : p_commands -> p_command list = fun cs ->
  match Stream.peek cs with
  | None -> []
  | Some c -> Stream.junk cs; c :: commands cs

(** [parse file] parses with the parser of Lambdapi the [file] produced by
    Carcara, which is a plain Lambdapi file. *)
let parse : string -> translation = fun file ->
  let commands = commands (Parser.parse_file file) in
  let symbol c = match c.elt with P_symbol s -> Some s | _ -> None in
  let symbols = List.filter_map symbol commands in
  let having r = List.filter (fun s -> role s = r) symbols in
  let lemmas = having Lemma in
  { commands
  ; constants = having Constant
  ; definitions = having Definition
  ; premises = having Premise
  ; lemmas
  ; theorem = List.nth_opt lemmas (List.length lemmas - 1) }

(** [statement s] is the statement of [s]: its type, quantified over its
    parameters. *)
let statement : p_symbol -> p_term = fun s ->
  let t = match s.p_sym_typ with Some t -> t | None -> Pos.none P_Wild in
  match s.p_sym_arg with [] -> t | xs -> Pos.none (P_Prod(xs, t))

(** {1 Abstraction over the constants and the premises}

    Carcara declares the constants of the problem and postulates its
    premises, as symbols, and its definitions and lemmas use them. To apply
    the theorem to the terms and the hypotheses of a goal, the constants and
    the premises are turned into parameters of every definition and
    lemma. *)

(** [abstracted s] is the name of the definition or lemma [s] once it takes
    the constants and the premises as parameters. *)
let abstracted : string -> string = fun s -> s ^ "_"

(** [rename f t] replaces in [t] each identifier [x] by [u] when [f x] is
    [Some u]. Binders are not taken into account: the names that [f]
    renames are not bound in the terms of a translation. *)
let rec rename : (string -> p_term option) -> p_term -> p_term = fun f t ->
  let mk elt = {t with elt} in
  let r = rename f in
  let params = List.map (fun (ids, a, b) -> ids, Option.map r a, b) in
  match t.elt with
  | P_Iden({elt=([],x);_}, false) ->
      (match f x with Some u -> u | None -> t)
  | P_Appl(u,v) -> mk (P_Appl(r u, r v))
  | P_Arro(u,v) -> mk (P_Arro(r u, r v))
  | P_Wrap u -> mk (P_Wrap(r u))
  | P_Expl u -> mk (P_Expl(r u))
  | P_Abst(xs,u) -> mk (P_Abst(params xs, r u))
  | P_Prod(xs,u) -> mk (P_Prod(params xs, r u))
  | P_LLet(x,xs,a,u,v) -> mk (P_LLet(x, params xs, Option.map r a, r u, r v))
  | P_Meta(m,ts) -> mk (P_Meta(m, Array.map r ts))
  | P_Patt(x,ts) -> mk (P_Patt(x, Option.map (Array.map r) ts))
  | P_Type | P_Wild | P_Iden _ | P_NLit _ | P_SLit _ -> t

(** [is_abstracted tr] tells whether [abstract tr] changes [tr]. *)
let is_abstracted : translation -> bool = fun tr ->
  tr.constants <> [] || tr.premises <> []

(** [abstract tr] is the list of the commands of [tr] where the constants
    and the premises are not declared anymore: each definition [d] is
    replaced by [abstracted d], which takes the constants as parameters,
    and each lemma [t] by [abstracted t], which takes the constants then
    the premises as its first parameters. In the types and the
    definitions, a name [d] is replaced by [abstracted d] applied to the
    constants. The proof of a lemma is unchanged, after tactics that give
    their meaning back to the names it may use: it assumes the constants
    and the premises, and it sets the name of each definition and of each
    previous lemma to its abstraction applied to them. The tactic that
    unfolds a definition by its name is renamed too. *)
let abstract : translation -> p_command list = fun tr ->
  let ident x = Pos.none (P_Iden(Pos.none ([], x), false)) in
  let name s = s.p_sym_nam.elt in
  let constants = List.map name tr.constants
  and premises = List.map name tr.premises
  and definitions = List.map name tr.definitions in
  let applied x args =
    let app t y = Pos.none (P_Appl(t, ident y)) in
    Pos.none (P_Wrap(List.fold_left app (ident (abstracted x)) args))
  in
  let definition x =
    if List.mem x definitions then Some (applied x constants) else None
  in
  let term = rename definition in
  let params = List.map (fun (ids, a, b) -> ids, Option.map term a, b) in
  let param s = [Some s.p_sym_nam], Option.map term s.p_sym_typ, false in
  let constant_params = List.map param tr.constants
  and premise_params = List.map param tr.premises in
  let step t = Tactic(Pos.none t, []) in
  let assume =
    let id x = Some (Pos.none x) in
    step (P_tac_assume (List.map id (constants @ premises)))
  in
  let set args x = step (P_tac_set(Pos.none x, applied x args)) in
  let renamed s extra =
    { s with p_sym_nam = {s.p_sym_nam with elt = abstracted (name s)}
    ; p_sym_arg = extra @ params s.p_sym_arg
    ; p_sym_typ = Option.map term s.p_sym_typ
    ; p_sym_trm = Option.map term s.p_sym_trm }
  in
  (* The tactic [simplify d] unfolds the symbol [d], which is now
     [abstracted d], a function of the constants: its unfolding is then
     β-reduced. *)
  let rec proofstep (Tactic(t, subproofs)) =
    let subproofs = List.map subproof subproofs in
    match t.elt with
    | P_tac_simpl(SimpSym({elt=([],x);_} as q))
      when List.mem x definitions ->
        let unfold = P_tac_simpl(SimpSym {q with elt = [], abstracted x}) in
        [Tactic({t with elt = unfold}, []);
         Tactic({t with elt = P_tac_simpl SimpBetaOnly}, subproofs)]
    | _ -> [Tactic(t, subproofs)]
  and subproof steps = List.concat_map proofstep steps in
  (* [previous] are the names of the lemmas before [c], last first. *)
  let command (previous, acc) c =
    match c.elt with
    | P_symbol s ->
        begin match role s, s.p_sym_prf with
        | (Constant | Premise), _ -> previous, acc
        | Definition, _ ->
            let s = renamed s constant_params in
            previous, {c with elt = P_symbol s} :: acc
        | Lemma, Some(proof, e) ->
            let intro =
              assume :: List.map (set constants) definitions
              @ List.rev_map (set (constants @ premises)) previous
            in
            let proof =
              match List.map subproof proof with
              | [] -> [intro]
              | first :: others -> (intro @ first) :: others
            in
            let s' = renamed s (constant_params @ premise_params) in
            let s' = {s' with p_sym_prf = Some(proof, e)} in
            name s :: previous, {c with elt = P_symbol s'} :: acc
        | Lemma, None -> previous, c :: acc
        end
    | _ -> previous, c :: acc
  in
  if is_abstracted tr
  then List.rev (snd (List.fold_left command ([], []) tr.commands))
  else tr.commands

(** [theorem_name tr] is the name of the theorem of [tr] in [abstract tr]. *)
let theorem_name : translation -> string option = fun tr ->
  let name s =
    if is_abstracted tr then abstracted s.p_sym_nam.elt
    else s.p_sym_nam.elt
  in
  Option.map name tr.theorem

(** {1 The translation in the current context} *)

open Core

(** [require ss mp] loads the module [mp], compiling it if needed, and makes
    the signature of [ss] depend on it. It is set by [Compile], which this
    module cannot depend on. *)
let require : (Sig_state.t -> Path.t -> Sig_state.t) Stdlib.ref =
  Stdlib.ref (fun _ _ -> assert false)

(** [quietly f x] is [f x] without the messages and the warnings that
    loading modules prints, and without its effect on how terms are
    printed afterwards. *)
let quietly : ('a -> 'b) -> 'a -> 'b = fun f x ->
  let verbose = Timed.(!Console.verbose)
  and default = Stdlib.(!Console.default_verbose)
  and warnings = Stdlib.(!Error.no_warnings)
  and printing = Timed.(!Print.sig_state) in
  let restore () =
    Stdlib.(Console.default_verbose := default);
    Stdlib.(Error.no_warnings := warnings);
    Timed.(Console.verbose := verbose);
    Timed.(Print.sig_state := printing)
  in
  Stdlib.(Console.default_verbose := 0);
  Stdlib.(Error.no_warnings := true);
  Timed.(Console.verbose := 0);
  Fun.protect ~finally:restore (fun () -> f x)

(** [missing ss tr] is the list of the modules that the translation [tr]
    requires (the ones of Carcara's library) and that the signature of [ss]
    does not depend on. *)
let missing : Sig_state.t -> translation -> Path.t list = fun ss tr ->
  let deps = Timed.(!(ss.signature.sign_deps)) in
  let paths c =
    match c.elt with
    | P_require(_, ps) -> List.map (fun p -> p.elt) ps
    | _ -> []
  in
  List.filter (fun p -> not (Path.Map.mem p deps))
    (List.concat_map paths tr.commands)

(** A translation that is loaded, which the goal has to be related to. *)
type reconstruction =
  { translation : translation
  ; file : string (** The Lambdapi file that is loaded. *)
  ; same_builtins : bool
    (** Whether the builtins of the current file are the ones of the
        translation, which its tactics rely on. *)
  ; theorem : Term.sym
    (** The theorem of the translation, which takes its constants and
        proofs of its premises. *) }

(** [load ss dir tr] loads in the current process the translation [tr],
    abstracted over its constants and premises (see [abstract]): it is
    written in the file [dir/reconstruction.lp], and loaded as the module
    [d.reconstruction] where [d] is the name of [dir]. The signature of
    [ss] then depends on it: its symbols can be used, qualified, in the
    current file. The modules of Carcara's library that it requires must
    already be loaded (see [missing]). It fails if the file does not
    type-check. *)
let load : Sig_state.t -> string -> translation -> reconstruction =
  fun ss dir tr ->
  let b = Buffer.create 4096 in
  let ppf = Format.formatter_of_buffer b in
  List.iter (Format.fprintf ppf "%a@." Pretty.command) (abstract tr);
  Format.pp_print_flush ppf ();
  let file = Filename.concat dir "reconstruction.lp" in
  write file (Buffer.contents b);
  let root = Filename.basename dir in
  Library.add_mapping ([root], dir);
  let mp = [root; "reconstruction"] in
  ignore (quietly (Stdlib.(!require) ss) mp);
  let sign = Path.Map.find mp Timed.(!Sign.loaded) in
  (* The builtins of the translation are the ones of the modules it depends
     on. *)
  let same_builtins =
    let module M = Lplib.Extra.StrMap in
    let add p _ m =
      match Path.Map.find_opt p Timed.(!Sign.loaded) with
      | Some d -> M.union (fun _ _ s -> Some s) m Timed.(!(d.sign_builtins))
      | None -> m
    in
    let theirs = Path.Map.fold add Timed.(!(sign.sign_deps)) M.empty in
    let same b s =
      match M.find_opt b ss.builtins with Some s' -> s' == s | None -> true
    in
    M.for_all same theirs
  in
  match theorem_name tr with
  | None -> fatal_no_pos "The translation has no theorem."
  | Some th ->
      {translation = tr; file; same_builtins; theorem = Sign.find sign th}

(** {1 Report (display only)}

    Nothing here changes what is translated, checked or parsed: it only
    reads the files and the messages left by the steps above, and prints
    them. *)

module Report = struct

  (** [first_line s] is the first non-empty line of [s], if any. *)
  let first_line : string -> string option = fun s ->
    List.find_opt (fun l -> l <> "")
      (List.map String.trim (String.split_on_char '\n' s))

  (** [or_none m] is the message [m], or that there is none. *)
  let or_none : string option -> string =
    Option.value ~default:"no error message"

  (** [carcara_error dir] is the first line of the messages of the last run
      of Carcara in [dir] (see [translate]), if any. *)
  let carcara_error : string -> string option = fun dir ->
    first_line (read (Filename.concat dir "carcara.err"))

  (** [translated pos file mode] prints that the Lambdapi [file] was produced
      by Carcara in [mode]. *)
  let translated : Pos.popt -> string -> string -> unit = fun pos file mode ->
    Console.out 1 "%a Carcara: translated (%s), in %s" Pos.pp pos mode file

  (** [replace sub by s] is [s] where the occurrences of [sub] are replaced
      by [by]. *)
  let replace : string -> string -> string -> string = fun sub by s ->
    let n = String.length sub and b = Buffer.create (String.length s) in
    let rec go i =
      if i >= String.length s then Buffer.contents b
      else if n > 0 && i + n <= String.length s && String.sub s i n = sub
      then (Buffer.add_string b by; go (i + n))
      else (Buffer.add_char b s.[i]; go (i + 1))
    in
    go 0

  (** [script pos r ~assumed ~constants ~premises ~statement ~goal] prints,
      as Lambdapi code that can replace the call to the why3 tactic, what
      the tactic does with the loaded
      translation [r]. First, the translation. It can be put in the
      current file only if the file has the builtins of Carcara's library,
      which the tactics of the translation rely on: otherwise, only that is
      printed. Then the proof: after the hypotheses
      [assumed], a hole (admitted) for each of the [constants] that no
      variable of the goal stands for, for each of the [premises] and from
      the [statement] of the theorem to the [goal], and the theorem applied
      to the constants and the premises. A constant is given with its
      type, its value, and whether that value is a hole. *)
  let script :
    Pos.popt -> reconstruction -> assumed:string list
    -> constants:(string * Term.term * Term.term * bool) list
    -> premises:Term.term list -> statement:Term.term -> goal:Term.term
    -> unit =
    fun pos r ~assumed ~constants ~premises ~statement ~goal ->
    let str pp x = Format.asprintf "%a" pp x in
    let valid i x =
      if String.starts_with ~prefix:"_" x then Printf.sprintf "h%d" i else x
    in
    let assumed = List.mapi valid assumed in
    (* A constant that is a hole is named after the constant. *)
    let hole_name x = x ^ "'" in
    let constant (x, _, v, hole) =
      if hole then hole_name x else str Print.term v
    in
    let term t =
      let s = str Print.term t in
      (* In the current file, the symbols of the translation are not
         qualified. *)
      let s = replace (str Path.pp r.theorem.sym_path ^ ".") "" s in
      let hole s (x, _, v, hole) =
        if hole then replace (str Print.term v) (hole_name x) s else s
      in
      List.fold_left hole s constants
    in
    let names = List.map (fun s -> s.p_sym_nam.elt) r.translation.premises in
    let have ppf (x, a) =
      Format.fprintf ppf "  have %s : %s { admit };@," x (term a)
    in
    let holes = List.filter (fun (_, _, _, hole) -> hole) constants in
    let hole ppf (x, a, _, _) = have ppf (hole_name x, a) in
    let assume ppf = function
      | [] -> ()
      | xs -> Format.fprintf ppf "  assume %s;@," (String.concat " " xs)
    in
    let list pp = Format.pp_print_list ~pp_sep:(fun _ () -> ()) pp in
    let holes_nb = List.length holes + List.length names + 1 in
    if r.same_builtins then
      Console.out 1
        "@[<v>%a Carcara: reconstruction with %d holes. To replace the \
         why3 tactic, put before the symbol:@,@,%s@,and replace the tactic \
         by:@,@,%a%a%a  have goal : (%s) → %s { admit };@,  \
         refine goal (%s);@]"
        Pos.pp pos holes_nb (read r.file)
        assume assumed (list hole) holes
        (list have) (List.combine names premises)
        (term statement) (term goal)
        (String.concat " "
           (r.theorem.sym_name :: List.map constant constants @ names))
    else
      Console.out 1
        "%a Carcara: reconstruction with %d holes. Its code cannot be \
         placed in this file, which does not use the encoding of Carcara's \
         library (the builtins are other symbols, so the tactics of the \
         translation would fail, and %d constants have no counterpart). To \
         get code to place here, state the goal with the Stdlib: require \
         open Stdlib.Set Stdlib.Prop Stdlib.FOL; (after the require of \
         alethe). The translation is in %s"
        Pos.pp pos holes_nb (List.length holes) r.file

  (** [not_loaded pos msg] prints that the translation cannot be loaded. *)
  let not_loaded : Pos.popt -> string -> unit = fun pos msg ->
    wrn pos "Carcara: the translation cannot be loaded: %s" msg

  (** [summary pos tr] prints the theorem of the translation [tr] and its
      premises. *)
  let summary : Pos.popt -> translation -> unit = fun pos tr ->
    let decl ppf s =
      Format.fprintf ppf "%s : %a" s.p_sym_nam.elt Pretty.term (statement s)
    in
    let steps = List.length tr.lemmas - Option.fold ~none:0 ~some:(fun _ -> 1)
                                           tr.theorem in
    match tr.theorem with
    | None -> wrn pos "Carcara: the translation has no theorem."
    | Some th ->
        let premises ppf = function
          | [] -> Format.fprintf ppf "without premises"
          | l ->
              Format.fprintf ppf "from the premises@,%a"
                (Format.pp_print_list
                   (fun ppf -> Format.fprintf ppf "  %a" decl)) l
        in
        Console.out 1
          "@[<v>%a Carcara: the translation proves@,  %a@,%a@,\
           (%d constants, %d definitions, %d proof steps)@]"
          Pos.pp pos decl th premises tr.premises
          (List.length tr.constants) (List.length tr.definitions) steps

  (** [file f] prints the content of the file [f]. *)
  let file : string -> unit = fun f -> Console.out 1 "%s" (read f)

  (** [no_translation pos dir reason] prints that Carcara gave no translation
      in [dir], with the messages of its last run, or [reason]. *)
  let no_translation : Pos.popt -> string -> string option -> unit =
    fun pos dir reason ->
    let msg =
      match carcara_error dir, reason with
      | Some m, _ | None, Some m -> m
      | None, None -> or_none None
    in
    wrn pos "Carcara: no translation (files in %s): %s" dir msg

end

(** {1 Reconstruction} *)

(** [output ss pos ~problem ~output] translates with Carcara the Alethe
    proof printed by the prover in [output] for the SMT-LIB [problem] (see
    [translate]), parses the Lambdapi file obtained (see [parse]) and loads
    it in the current process (see [load]). It fails if the current file
    does not require the modules of Carcara's library that the translation
    uses (see [missing]). Carcara reads the output of the
    prover as it is (["unsat"], then the proof in parentheses). The
    translation is first tried strictly, then with "--admit-unsupported".
    The files are kept in a fresh temporary directory. The steps are
    printed when debugging (see [Report]). The result is [None] if there is
    no translation, or if it cannot be loaded. *)
let output :
  Sig_state.t -> Pos.popt -> problem:string -> output:string
  -> reconstruction option =
  fun ss pos ~problem ~output ->
  let dir = Filename.temp_dir "lambdapi_carcara_" "" in
  let file f = Filename.concat dir f in
  write (file "problem.smt2") problem;
  write (file "proof.alethe") output;
  let proof = file "proof.lp" in
  let after_translation mode =
    if Logger.log_enabled() then
      (Report.translated pos proof mode; Report.file proof);
    let time = Timed.Time.save () in
    match parse proof with
    | exception Fatal(_, msg, _) -> Report.not_loaded pos msg; None
    | tr ->
        if Logger.log_enabled() then Report.summary pos tr;
        (* Carcara's library is not loaded behind the back of the user. *)
        begin match missing ss tr with
        | [] -> ()
        | ps ->
            fatal pos "The reconstruction of this proof uses Carcara's \
                       library. Add to the file: require %s;"
              (String.concat " " (List.map (Format.asprintf "%a" Path.pp) ps))
        end;
        match load ss dir tr with
        | r -> Some r
        | exception Fatal(_, msg, _) ->
            Timed.Time.restore time; Report.not_loaded pos msg; None
  in
  if translate dir [] then after_translation "strict"
  else
    let reason = Report.carcara_error dir in
    if translate dir ["--admit-unsupported"] then
      after_translation
        ("--admit-unsupported, strict failed: " ^ Report.or_none reason)
    else (Report.no_translation pos dir reason; None)
