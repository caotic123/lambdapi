(** Test of the coherent preprocessing ("Morleyization") of why3 tactic goals
    and of the classical fallback. No proof reconstruction: the test asks
    CVC5 for proofs of the preprocessed problems and reports which classical
    axioms those proofs use (the leftovers).

    From the repository root:
    {v
    dune exec tests/constructionism/constructionism_why3_test.exe -- \
      [--driver FILE] [--cvc5-options OPTS] [--timeout SEC] [--out DIR] \
      [--quiet] \
      tests/constructionism/problems.lp tests/why3_examples/*.lp \
      tests/OK/why3.lp
    v}
    The problems of a file are its calls to the why3 tactic (the goal at the
    call; the call itself is replaced by admit) and its symbols of type
    [Π x̄, π G] whose proof does not call why3 (see [Problems.load]).

    Design: AGENTS.md, "Replay design: intuitionistic first, classical
    fallback". Module [Morley] is the part meant to move to src/handle; the
    modules after it are test harness. *)

(* PSEUDO-CODE
   ===========

   Input: a Why3 task  H₁ … Hₙ ⊢ G  built by Why3_tactic.translate_goal.

   Vocabulary:
     coherent formula       built from atoms, ⊤, ⊥, ∧, ∨, ∃;
     geometric implication  ∀x̄. φ → ψ  with φ and ψ coherent.
   If the hypotheses are geometric implications and the goal is coherent,
   replaying the classical proof with r := G (Friedman's A-translation)
   needs no excluded middle (EM). Traversié 2025, Lemma 16, translates any
   classical proof; geometric hypotheses H give H^T by the unit H → T H,
   and a coherent goal has G^T = T G (AGENTS.md, "Replay design"). Barr's
   theorem (Negri 2003) only says that some intuitionistic proof exists,
   not that CVC5's proof can be translated.

   Output: one task per subgoal, made of geometric implications and a
   coherent goal, together with
     ⟦R⟧ for every fresh predicate R: the subformula of the input that R
         stands for (the replay instantiates R := ⟦R⟧);
     a kind for every axiom:
       Hyp      piece of an input hypothesis or of a goal premise;
       Def      intuitionistically provable once every R := ⟦R⟧;
       Tot_em   A ∨ R with ⟦R⟧ = ¬A or A → B: classical, follows from A ∨ ¬A;
       Tot_all  R ∨ ∃x. R' with ⟦R⟧ = ∀x. B and ⟦R'⟧ = ¬B: classical.

   split_goal(Γ, G)                  -- intuitionistic introduction steps
     ∀x. B   → split_goal(Γ, B[x := c])        c fresh constant
     A → B   → split_goal(Γ ∪ {A}, B)
     ¬A      → split_goal(Γ ∪ {A}, ⊥)
     A ∧ B   → split_goal(Γ, A) ++ split_goal(Γ, B)
     A ⇔ B   → split_goal(Γ, A → B) ++ split_goal(Γ, B → A)
     other   → [(Γ, G)]

   for each subgoal (Γ, G') of split_goal([], G):
     Ax := []
     for each H in H₁ … Hₙ, Γ:  hyp(Hyp, [], [], H)
     task := Ax ⊢ neg(G')

   hyp(k, x̄, prems, H)              -- adds ∀x̄. ⋀prems → H, made geometric
     ∀ȳ. B   → hyp(k, x̄ȳ, prems, B)
     A → B   → hyp(k, x̄, prems ++ [neg(A)], B)
     ¬A      → hyp(k, x̄, prems ++ [neg(A)], ⊥)
     A ∧ B   → hyp(k, x̄, prems, A); hyp(k, x̄, prems, B)
     A ⇔ B   → hyp(k, x̄, prems, A → B); hyp(k, x̄, prems, B → A)
     other   → Ax += (k, ∀x̄. ⋀prems → pos(H))

   pos(φ)    -- φ is available: coherent φ⁺ such that φ⁺ ⊢ φ
     atom    → φ
     ∧ ∨ ∃   → componentwise
     other   → R fresh, ȳ := fv(φ), ⟦R⟧ := φ,
               hyp(Def, ȳ, [R ȳ], φ)                  -- ∀ȳ. R ȳ → φ
               return R ȳ

   neg(φ)    -- φ must be produced: coherent φ⁻ such that φ ⊢ φ⁻
     atom    → φ
     ∧ ∨ ∃   → componentwise
     A ⇔ B   → neg(A → B) ∧ neg(B → A)
     other   → R fresh, ȳ := fv(φ), ⟦R⟧ := φ, add the axioms below, return R ȳ
       ¬A    : Tot_em   ∀ȳ. pos(A) ∨ R ȳ        instance  A ∨ ¬A
       A → B : Tot_em   ∀ȳ. pos(A) ∨ R ȳ        instance  A ∨ (A → B)
               Def      ∀ȳ. neg(B) → R ȳ        instance  B → (A → B)
       ∀x. B : Tot_all  ∀ȳ. R ȳ ∨ ∃x. pos(¬B)   instance  (∀x. B) ∨ ∃x. ¬B

   Only one direction is needed per occurrence: R ⊢ ⟦R⟧ where R occurs
   positively, ⟦R⟧ ⊢ R where it occurs negatively. So every model of the new
   task gives a model of the input, and a classically provable input stays
   classically provable. The test reports "LOST" when CVC5 proves the input
   but not the new task (so far only by lack of quantifier instantiations:
   try --cvc5-options=--enum-inst).

   Mode 1, r := G (Friedman). Replay CVC5's proof of the new task, generic in
   the fresh predicates, then instantiate them. Leftovers: the Tot_em and
   Tot_all axioms the proof uses.

   Mode 2, r := ⊥ (Glivenko), on the same proof. Hypotheses enter as ¬¬H:
   free for Hyp and Def, and for Tot_em because ¬¬(A ∨ ¬A) is
   intuitionistic, but not for Tot_all (that needs the double-negation
   shift). The result is ¬¬G'; leftover ¬¬G' → G' unless G' is stable (built
   from ⊥, ¬, ∧, ⇔, → and ∀ with stable conclusions). If CVC5 does not prove
   the new task, mode 2 uses the proof of the input task, with leftover
   ¬¬G → G.

   A problem is solved without EM when every subgoal has a mode with no
   leftover. In both modes, bind and sko_* steps need the double-negation
   shift in the clause-level reading; they are counted separately. *)

(** {1 The transformation} *)

module Morley = struct
  open Why3
  open Term

  (** Kind of an axiom of a transformed task. *)
  type kind =
    | Hyp of string
    (** Piece of the input hypothesis with this name ("goal" for a premise
        introduced from the goal). *)
    | Def
    (** Intuitionistically provable once the fresh predicates are replaced
        by their meanings. *)
    | Tot_em
    (** [∀ȳ. A ∨ R ȳ] with [⟦R⟧ = ¬A] or [A → B]. *)
    | Tot_all
    (** [∀ȳ. R ȳ ∨ ∃x. R' ȳ x] with [⟦R⟧ = ∀x. B] and [⟦R'⟧ = ¬B]. *)

  let tag : kind -> string = function
    | Hyp _ -> "hyp" | Def -> "def" | Tot_em -> "tot" | Tot_all -> "totall"

  (** Shape of a formula, as far as the transformation is concerned. *)
  type shape =
    | Atom (** predicate application, equality, true, false, or other *)
    | And of term * term
    | Or of term * term
    | Imp of term * term
    | Iff of term * term
    | Not of term
    | All of vsymbol list * term
    | Ex of vsymbol list * term

  let shape (f : term) : shape =
    match f.t_node with
    | Tbinop (Tand, a, b) -> And (a, b)
    | Tbinop (Tor, a, b) -> Or (a, b)
    | Tbinop (Timplies, a, b) -> Imp (a, b)
    | Tbinop (Tiff, a, b) -> Iff (a, b)
    | Tnot a -> Not a
    | Tquant (Tforall, q) -> let xs, _, b = t_open_quant q in All (xs, b)
    | Tquant (Texists, q) -> let xs, _, b = t_open_quant q in Ex (xs, b)
    | _ -> Atom

  (** State of the transformation of one subgoal. *)
  type state =
    { mutable preds : (lsymbol * (vsymbol list * term)) list
    (** Fresh predicates [R] with their meaning [λȳ. ⟦R⟧], newest first. *)
    ; mutable axioms : (kind * term) list (** Newest first. *) }

  let free_vars (f : term) : vsymbol list =
    Mvs.keys (t_freevars Mvs.empty f)

  (** [forall xs f] quantifies [f] over the variables of [xs] free in [f]. *)
  let forall (xs : vsymbol list) (f : term) : term =
    let fv = t_freevars Mvs.empty f in
    match List.filter (fun x -> Mvs.mem x fv) xs with
    | [] -> f
    | xs -> t_forall_close xs [] f

  let exists (xs : vsymbol list) (f : term) : term =
    if xs = [] then f else t_exists_close xs [] f

  let implies (prems : term list) (f : term) : term =
    if prems = [] then f else t_implies (t_and_l prems) f

  let add (st : state) (k : kind) (f : term) : unit =
    st.axioms <- (k, f) :: st.axioms

  (** [fresh st phi] declares a fresh predicate [R] meaning [phi] and
      returns [ȳ] and [R ȳ], where [ȳ] are the free variables of [phi]. *)
  let fresh (st : state) (phi : term) : vsymbol list * term =
    let ys = free_vars phi in
    let name = Printf.sprintf "R%d" (List.length st.preds + 1) in
    let r =
      create_psymbol (Ident.id_fresh name) (List.map (fun y -> y.vs_ty) ys)
    in
    st.preds <- (r, (ys, phi)) :: st.preds;
    ys, ps_app r (List.map t_var ys)

  (** [hyp st k xs prems h] adds the axioms of kind [k] that make
      [∀xs. ⋀prems → h] geometric. *)
  let rec hyp (st : state) (k : kind) xs prems (h : term) : unit =
    match shape h with
    | All (ys, b) -> hyp st k (xs @ ys) prems b
    | Imp (a, b) -> hyp st k xs (prems @ [neg st a]) b
    | Not a -> hyp st k xs (prems @ [neg st a]) t_false
    | And (a, b) -> hyp st k xs prems a; hyp st k xs prems b
    | Iff (a, b) ->
        hyp st k xs prems (t_implies a b); hyp st k xs prems (t_implies b a)
    | Atom | Or _ | Ex _ ->
        let head = pos st h in
        add st k (forall xs (implies prems head))

  (** [pos st phi] is a coherent formula that implies [phi] once the fresh
      predicates are instantiated. [phi] is available (positive
      occurrence). *)
  and pos (st : state) (phi : term) : term =
    match shape phi with
    | Atom -> phi
    | And (a, b) -> t_and (pos st a) (pos st b)
    | Or (a, b) -> t_or (pos st a) (pos st b)
    | Ex (xs, b) -> exists xs (pos st b)
    | Imp _ | Iff _ | Not _ | All _ ->
        let ys, r = fresh st phi in
        hyp st Def ys [r] phi;
        r

  (** [neg st phi] is a coherent formula that [phi] implies, classically,
      given the new axioms. [phi] must be produced (negative occurrence). *)
  and neg (st : state) (phi : term) : term =
    match shape phi with
    | Atom -> phi
    | And (a, b) -> t_and (neg st a) (neg st b)
    | Or (a, b) -> t_or (neg st a) (neg st b)
    | Ex (xs, b) -> exists xs (neg st b)
    | Iff (a, b) -> t_and (neg st (t_implies a b)) (neg st (t_implies b a))
    | Not a ->
        let ys, r = fresh st phi in
        add st Tot_em (forall ys (t_or (pos st a) r));
        r
    | Imp (a, b) ->
        let ys, r = fresh st phi in
        add st Tot_em (forall ys (t_or (pos st a) r));
        if b.t_node <> Tfalse then
          add st Def (forall ys (t_implies (neg st b) r));
        r
    | All (xs, b) ->
        let ys, r = fresh st phi in
        add st Tot_all (forall ys (t_or r (exists xs (pos st (t_not b)))));
        r

  (** [split_goal consts prems g] applies the introduction steps to [g] and
      returns one [(constants, premises, conclusion)] per subgoal. *)
  let rec split_goal consts prems (g : term) =
    match shape g with
    | All (xs, b) ->
        let mk x = create_fsymbol (Ident.id_clone x.vs_name) [] x.vs_ty in
        let cs = List.map mk xs in
        let add s x c = Mvs.add x (fs_app c [] x.vs_ty) s in
        let b = t_subst (List.fold_left2 add Mvs.empty xs cs) b in
        split_goal (consts @ cs) prems b
    | Imp (a, b) -> split_goal consts (prems @ [a]) b
    | Not a -> split_goal consts (prems @ [a]) t_false
    | And (a, b) -> split_goal consts prems a @ split_goal consts prems b
    | Iff (a, b) ->
        split_goal consts prems (t_implies a b)
        @ split_goal consts prems (t_implies b a)
    | Atom | Or _ | Ex _ -> [consts, prems, g]

  (** A transformed subgoal. *)
  type subgoal =
    { consts : lsymbol list (** Constants introduced from the goal. *)
    ; preds : (lsymbol * (vsymbol list * term)) list
    (** Fresh predicates with their meanings. *)
    ; axioms : (string * kind * term) list (** Named axioms, in order. *)
    ; goal : term (** Coherent goal. *)
    ; concl : term (** The conclusion G' that [goal] stands for. *) }

  (** [transform hyps g] transforms the problem [hyps ⊢ g]. *)
  let transform (hyps : (string * term) list) (g : term) : subgoal list =
    let subgoal (consts, prems, concl) =
      let st = {preds = []; axioms = []} in
      List.iter (fun (name, h) -> hyp st (Hyp name) [] [] h) hyps;
      List.iter (hyp st (Hyp "goal") [] []) prems;
      let goal = neg st concl in
      let name i (k, f) = Printf.sprintf "%s%d" (tag k) (i + 1), k, f in
      { consts; preds = List.rev st.preds; goal; concl
      ; axioms = List.mapi name (List.rev st.axioms) }
    in
    List.map subgoal (split_goal [] [] g)

  (** [instance preds f] replaces in [f] every fresh predicate of [preds] by
      its meaning. *)
  let rec instance preds (f : term) : term =
    match f.t_node with
    | Tapp (r, args) when List.mem_assq r preds ->
        let ys, phi = List.assq r preds in
        let add s y a = Mvs.add y a s in
        t_subst (List.fold_left2 add Mvs.empty ys args) phi
    | _ -> t_map (instance preds) f

  (** [stable f] is a syntactic sufficient condition for [¬¬f → f] to be
      intuitionistically provable. *)
  let rec stable (f : term) : bool =
    match shape f with
    | Not _ -> true
    | Atom -> f.t_node = Ttrue || f.t_node = Tfalse
    | And (a, b) | Iff (a, b) -> stable a && stable b
    | Imp (_, b) | All (_, b) -> stable b
    | Or _ | Ex _ -> false

  let rec coherent (f : term) : bool =
    match shape f with
    | Atom -> true
    | And (a, b) | Or (a, b) -> coherent a && coherent b
    | Ex (_, b) -> coherent b
    | Imp _ | Iff _ | Not _ | All _ -> false

  let rec geometric (f : term) : bool =
    match shape f with
    | All (_, b) -> geometric b
    | Imp (a, b) -> coherent a && coherent b
    | _ -> coherent f

  (** [split_task task] returns the declarations (types and symbols), the
      named hypotheses and the goal of a task built by
      [Why3_tactic.translate_goal]. *)
  let split_task (task : Task.task) =
    let f (ds, hs, g) (d : Decl.decl) =
      match d.d_node with
      | Dprop (Paxiom, pr, h) -> ds, (pr.pr_name.id_string, h) :: hs, g
      | Dprop (Pgoal, _, g) -> ds, hs, Some g
      | _ -> d :: ds, hs, g
    in
    match List.fold_left f ([], [], None) (Task.task_decls task) with
    | ds, hs, Some g -> List.rev ds, List.rev hs, g
    | _, _, None -> invalid_arg "split_task: no goal"

  (** [task_of_subgoal ds sg] builds the task of [sg] on the declarations
      [ds]. *)
  let task_of_subgoal (ds : Decl.decl list) (sg : subgoal) : Task.task =
    let t = List.fold_left Task.add_decl None ds in
    let t = List.fold_left Task.add_param_decl t sg.consts in
    let t = List.fold_left (fun t (r, _) -> Task.add_param_decl t r) t sg.preds in
    let axiom t (name, _, f) =
      let pr = Decl.create_prsymbol (Ident.id_fresh name) in
      Task.add_prop_decl t Paxiom pr f
    in
    let t = List.fold_left axiom t sg.axioms in
    let g = Decl.create_prsymbol (Ident.id_fresh "G") in
    Task.add_prop_decl t Pgoal g sg.goal
end

(** {1 Calling CVC5 and reading its proof} *)

module Cvc5 = struct
  open Parsing.AletheSyntax

  let command = ref (Option.value (Sys.getenv_opt "CVC5") ~default:"cvc5")
  let extra_options = ref ""
  let timeout = ref 10
  let driver_file = ref "cvc5.drv"
  let out_dir : string option ref = ref None

  let driver =
    lazy (Why3.Driver.load_driver_file_and_extras
            Handle.Why3_tactic.why3_main Handle.Why3_tactic.why3_env
            ~extra_dir:None !driver_file [])

  (** [smtlib task] is the SMT-LIB problem the driver makes of [task]. *)
  let smtlib (task : Why3.Task.task) : string =
    let drv = Lazy.force driver in
    let buf = Buffer.create 1024 in
    let fmt = Format.formatter_of_buffer buf in
    let task = Why3.Driver.prepare_task drv task in
    ignore (Why3.Driver.print_task_prepared drv fmt task);
    Format.pp_print_flush fmt ();
    Buffer.contents buf

  (** [run name smt] runs CVC5 on [smt], asking for an Alethe proof with the
      options of the why3 tactic, and returns its standard output. *)
  let run (name : string) (smt : string) : string =
    let file, out =
      match !out_dir with
      | Some d ->
          Filename.concat d (name ^ ".smt2"), Filename.concat d (name ^ ".out")
      | None -> Filename.temp_file name ".smt2", Filename.temp_file name ".out"
    in
    Out_channel.with_open_bin file (fun oc -> output_string oc smt);
    let cmd =
      Printf.sprintf "%s %s %s --tlimit=%d %s > %s 2> /dev/null" !command
        Handle.Why3_tactic.cvc5_proof_options !extra_options (1000 * !timeout)
        (Filename.quote file) (Filename.quote out)
    in
    ignore (Sys.command cmd);
    let output = In_channel.with_open_bin out In_channel.input_all in
    if !out_dir = None then (Sys.remove file; Sys.remove out);
    output

  type answer =
    | Unsat of command list (** with the Alethe proof *)
    | Other of string (** first line of the output: sat, unknown, … *)

  let answer (output : string) : answer =
    let lines =
      String.split_on_char '\n' output
      |> List.map String.trim |> List.filter (( <> ) "")
    in
    match lines with
    | "unsat" :: rest ->
        (* Test only: drop CVC5's "(" … ")" wrapper around the proof. *)
        let rest =
          match rest with
          | "(" :: r ->
              (match List.rev r with ")" :: r -> List.rev r | _ -> r)
          | r -> r
        in
        begin
          match List.find_opt (String.starts_with ~prefix:"(error") rest with
          | Some e -> Other ("unsat, without Alethe proof: " ^ e)
          | None ->
              try
                let cmds = ref [] in
                Stream.iter
                  (fun (c : command Common.Pos.loc) -> cmds := c.elt :: !cmds)
                  (Parsing.Parser.Alethe.parse_string "cvc5"
                     (String.concat "\n" rest));
                Unsat (List.rev !cmds)
              with Common.Error.Fatal (_, msg, _) ->
                Other ("unsat, but the proof does not parse: " ^ msg)
        end
    | l :: _ -> Other l
    | [] -> Other "no output"

  (** [norm names t] removes the annotations of [t] and expands the [@p_n]
      names, recording in [names] the ones [t] defines. *)
  let rec norm names (t : term) : term =
    match t with
    | Annot (t, attrs) ->
        let t = norm names t in
        let define = function
          | "named", Some (SSymbol n) -> Hashtbl.replace names n t
          | _ -> ()
        in
        List.iter define attrs; t
    | Symbol s -> Option.value (Hashtbl.find_opt names s) ~default:t
    | Const _ -> t
    | App (f, ts) -> App (f, List.map (norm names) ts)
    | Forall (xs, t) -> Forall (xs, norm names t)
    | Exists (xs, t) -> Exists (xs, norm names t)
    | Choice (x, t) -> Choice (x, norm names t)
    | Let (bs, t) ->
        Let (List.map (fun (x, u) -> x, norm names u) bs, norm names t)

  let starts_with (s : string) (i : int) (p : string) : bool =
    let n = String.length p in
    i + n <= String.length s && String.sub s i n = p

  (** [closing s i] is the index just after the parenthesis that closes the
      one at index [i] of [s]. *)
  let closing (s : string) (i : int) : int =
    let n = String.length s in
    let skip i c = Option.value (String.index_from_opt s i c) ~default:n in
    let rec go i depth =
      if i >= n then n
      else match s.[i] with
        | '(' -> go (i + 1) (depth + 1)
        | ')' -> if depth = 1 then i + 1 else go (i + 1) (depth - 1)
        | '"' | '|' as c -> go (skip (i + 1) c + 1) depth
        | _ -> go (i + 1) depth
    in
    go i 0

  (** [assertions smt] lists [(name, φ)] for every [(assert φ)] of [smt],
      where [name] comes from the [;; "name"] comment Why3 prints before
      it. *)
  let assertions (smt : string) : (string * term) list =
    let n = String.length smt in
    let rec loop i name acc =
      if i >= n then List.rev acc
      else if starts_with smt i ";;" then
        let j = Option.value (String.index_from_opt smt i '\n') ~default:n in
        let line = String.sub smt i (j - i) in
        let name =
          if starts_with line 0 ";; \"" || starts_with line 0 ";; Goal \""
          then
            let a = String.index line '"' and b = String.rindex line '"' in
            String.sub line (a + 1) (b - a - 1)
          else name
        in
        loop j name acc
      else if starts_with smt i "(assert" then
        let j = closing smt i in
        let text = "(assume h" ^ String.sub smt (i + 7) (j - i - 7) in
        let acc =
          match
            Stream.next (Parsing.Parser.Alethe.parse_string "smt2" text)
          with
          | {elt = Assume (_, t, _); _} ->
              (name, norm (Hashtbl.create 1) t) :: acc
          | _ -> acc
        in
        loop j name acc
      else loop (i + 1) name acc
    in
    loop 0 "" []

  type proof_info =
    { used : string list (** Names of the assertions the proof uses. *)
    ; unmatched : int (** Used assumptions that match no assertion. *)
    ; rules : (string * int) list (** Rules of the used steps, with counts. *)
    }

  (** [analyse smt cmds] finds what the proof [cmds] of [smt] uses, going
      back from its last [(cl)] step. CVC5 prints an [assume] for every
      assertion, used or not. *)
  let analyse (smt : string) (cmds : command list) : proof_info =
    let tbl = Hashtbl.create 97 and anchors = Hashtbl.create 7 in
    let index = function
      | Assume (id, _, _) as c -> Hashtbl.replace tbl id c
      | Step s as c -> Hashtbl.replace tbl s.id c
      | Anchor (id, _, _) -> Hashtbl.replace anchors id ()
      | DefineFun _ -> ()
    in
    List.iter index cmds;
    let top id = not (String.contains id '.') in
    let final acc = function
      | Step s when s.clause = [] && top s.id -> Some s.id
      | _ -> acc
    in
    let seen = Hashtbl.create 97 in
    let rec visit id =
      if not (Hashtbl.mem seen id) then begin
        Hashtbl.add seen id ();
        (match Hashtbl.find_opt tbl id with
         | Some (Step s) -> List.iter visit s.premises
         | _ -> ());
        if Hashtbl.mem anchors id then
          let inner id' _ acc =
            if starts_with id' 0 (id ^ ".") then id' :: acc else acc in
          List.iter visit (Hashtbl.fold inner tbl [])
      end
    in
    Option.iter visit (List.fold_left final None cmds);
    let asserts = assertions smt and names = Hashtbl.create 97 in
    let count r rules =
      let k = Option.value (List.assoc_opt r rules) ~default:0 in
      (r, k + 1) :: List.remove_assoc r rules
    in
    let f info = function
      | Assume (id, t, _) ->
          let t = norm names t in
          if not (top id && Hashtbl.mem seen id) then info
          else begin match List.find_opt (fun (_, u) -> u = t) asserts with
            | Some (name, _) -> {info with used = name :: info.used}
            | None -> {info with unmatched = info.unmatched + 1}
          end
      | Step s when Hashtbl.mem seen s.id ->
          {info with rules = count s.rule info.rules}
      | _ -> info
    in
    let info =
      List.fold_left f {used = []; unmatched = 0; rules = []} cmds in
    {info with used = List.rev info.used; rules = List.rev info.rules}
end

(** {1 Problems} *)

module Problems = struct
  open Core
  open Common
  open Parsing.Syntax

  type problem =
    { file : string (** Base name of the file, without extension. *)
    ; name : string
    (** The symbol; [s.k] for the k-th why3 call (k ≥ 2) in its proof. *)
    ; task : (Why3.Task.task, string) result
    (** The task, or why it could not be built. *) }

  (** Names of the leading products of [t], without reduction, as the why3
      tactic computes them ([Tactic.get_prod_ids env false]). *)
  let rec prod_ids (t : Term.term) : string list =
    match Term.get_args t with
    | Term.Prod (_, b), _ ->
        let x, b = Term.unbind b in Term.base_name x :: prod_ids b
    | _ -> []

  let translate ss pos env g =
    try Ok (Handle.Why3_tactic.translate_goal ss pos env g)
    with Error.Fatal (_, msg, _) -> Error msg

  let is_prf ss (g : Term.term) =
    match Term.get_args g with
    | Term.Symb p, [_] ->
        (try p == Builtin.get ss None [] "Prf" with Error.Fatal _ -> false)
    | _ -> false

  (** [intro ss d pos ps] introduces the products of the focused goal, as
      the why3 tactic does before translating it. *)
  let intro ss (d : Handle.Command.proof_data) pos
      (ps : Handle.Proof.proof_state) =
    match ps.proof_goals with
    | Handle.Goal.Typ gt :: _ ->
        begin match prod_ids gt.goal_type with
        | [] -> ps
        | ids ->
            let idopts = Env.gen_valid_idopts gt.goal_hyps ids in
            fst (Handle.Tactic.handle ss d.pdata_sym_pos d.pdata_prv (ps, None)
                   (Pos.make pos (P_tac_assume idopts)) 0)
        end
    | _ -> ps

  (** Package files already mapped: a package root can be mapped only
      once. *)
  let packages : (string, unit) Hashtbl.t = Hashtbl.create 3

  (** [load file] checks [file] command by command, like
      [Handle.Compile.compile_file], and returns its problems in order:
      - every call to the why3 tactic in a proof, with the goal at that
        point, after the tactic's own introductions; the call is then
        replaced by [admit], so no prover runs;
      - every symbol of type [Π x̄, π G] whose proof does not call why3 (or
        that has no proof), with [x̄] introduced.
      A command that fails is reported and skipped. *)
  let load (file : string) : problem list =
    begin match Parsing.Package.find file with
    | Some cfg when Hashtbl.mem packages cfg -> ()
    | cfg ->
        Option.iter (fun cfg -> Hashtbl.add packages cfg ()) cfg;
        Parsing.Package.set_root_path file
    end;
    let mp = Library.path_of_file Parsing.LpLexer.escape file in
    let sign = Sign.create mp in
    Timed.(Sign.loaded := Path.Map.add mp sign !Sign.loaded);
    Timed.(Sign.loading := mp :: !Sign.loading);
    let base = Filename.remove_extension (Filename.basename file) in
    let problems = ref [] in
    let add name task = problems := {file = base; name; task} :: !problems in
    let ss = ref (Sig_state.of_sign sign) in
    let command (cmd : p_command) =
      LibMeta.reset_meta_counter ();
      try
        match Handle.Command.get_proof_data Handle.Compile.compile !ss cmd with
        | ss', None, _ -> ss := ss'
        | ss', Some d, _ ->
            let name =
              match cmd.elt with P_symbol s -> s.p_sym_nam.elt | _ -> "?"
            in
            let calls = ref 0 in
            let tactic r (t : p_tactic) n =
              match t.elt with
              | P_tac_why3 _ ->
                  incr calls;
                  let ps = intro ss' d t.pos (fst r) in
                  begin match ps.proof_goals with
                  | Handle.Goal.Typ gt :: _ ->
                      add (if !calls = 1 then name
                           else Printf.sprintf "%s.%d" name !calls)
                        (translate ss' t.pos gt.goal_hyps gt.goal_type)
                  | _ -> ()
                  end;
                  Handle.Tactic.handle ss' d.pdata_sym_pos d.pdata_prv
                    (ps, None) {t with elt = P_tac_admit} n
              | _ -> Handle.Tactic.handle ss' d.pdata_sym_pos d.pdata_prv r t n
            in
            let ps, _ = fold_proof tactic (d.pdata_state, None) d.pdata_proof in
            ss := d.pdata_finalize ss' ps;
            if !calls = 0 then
              match
                Lplib.Extra.StrMap.find_opt name Timed.(!(sign.sign_symbols))
              with
              | None -> ()
              | Some s ->
                  let ty = Timed.(!(s.sym_type)) in
                  let n = List.length (prod_ids ty) in
                  let env, g = Env.of_prod_nth [] n ty in
                  if is_prf !ss g then add name (translate !ss s.sym_pos env g)
      with Error.Fatal (pos, msg, _) ->
        Format.printf "%a: %s (command skipped)@." Pos.pp (Option.join pos) msg
    in
    Debug.stream_iter command (Parsing.Parser.parse_file file);
    Timed.(Sign.loading := List.tl !Sign.loading);
    List.rev !problems
end

(** {1 Polymorphic tasks}

    Test-only workaround for "Polymorphic tasks crash" (AGENTS.md): a
    variable [a : Set] of the context becomes a Why3 type variable, which the
    SMT-LIB printer rejects. As planned there, replace every type variable
    by a fresh abstract type. Remove this once why3_tactic.ml does it. *)

module Mono = struct
  open Why3

  (** [monomorphise task] returns [task] with its type variables replaced by
      abstract types, and the names of these variables. *)
  let monomorphise (task : Task.task) : Task.task * string list =
    let decls = Task.task_decls task in
    let add_tvs (s : Ty.Stv.t) (d : Decl.decl) =
      match d.d_node with
      | Dparam ls ->
          List.fold_left Ty.ty_freevars s
            (Option.to_list ls.ls_value @ ls.ls_args)
      | Dprop (_, _, f) -> Term.t_ty_freevars s f
      | _ -> s
    in
    let tvs = List.fold_left add_tvs Ty.Stv.empty decls in
    if Ty.Stv.is_empty tvs then task, []
    else
      let tss =
        Ty.Stv.fold (fun tv m ->
            Ty.Mtv.add tv
              (Ty.create_tysymbol (Ident.id_clone tv.tv_name) [] Ty.NoDef) m)
          tvs Ty.Mtv.empty
      in
      let inst = Ty.ty_inst (Ty.Mtv.map (fun ts -> Ty.ty_app ts []) tss) in
      let lss = ref Term.Mls.empty in
      let decl t (d : Decl.decl) =
        match d.d_node with
        | Dparam ls when not (Ty.Stv.is_empty (add_tvs Ty.Stv.empty d)) ->
            let ls' =
              Term.create_lsymbol (Ident.id_clone ls.ls_name)
                (List.map inst ls.ls_args) (Option.map inst ls.ls_value)
            in
            lss := Term.Mls.add ls ls' !lss;
            Task.add_param_decl t ls'
        | Dprop (k, pr, f) ->
            let ls l = Term.Mls.find_def l l !lss in
            Task.add_prop_decl t k pr (Term.t_s_map inst ls f)
        | _ -> Task.add_decl t d
      in
      let t = Ty.Mtv.fold (fun _ ts t -> Task.add_ty_decl t ts) tss None in
      List.fold_left decl t decls,
      List.map (fun (tv : Ty.tvsymbol) -> tv.tv_name.id_string)
        (Ty.Stv.elements tvs)
end

(** {1 Report} *)

module Report = struct
  open Why3

  let quiet = ref false

  let say fmt =
    if !quiet then Format.ifprintf Format.std_formatter fmt
    else Format.printf fmt

  let term = Pretty.print_term
  let str f = Format.asprintf "%a" term f

  (** Rules that need the double-negation shift in the clause reading. *)
  let dns_rules = ["bind"; "sko_ex"; "sko_forall"]

  let dns (info : Cvc5.proof_info) : int =
    List.fold_left
      (fun n (r, k) -> if List.mem r dns_rules then n + k else n)
      0 info.rules

  let rules ppf (info : Cvc5.proof_info) =
    let rule ppf (r, k) = Format.fprintf ppf "%s×%d" r k in
    Format.pp_print_list ~pp_sep:Format.pp_print_space rule ppf info.rules

  (** Outcome of a replay mode: [None] if there is no proof, otherwise the
      leftover goals ([[]]: no EM needed). *)
  type mode = string list option

  type row =
    { file : string
    ; name : string
    ; classical : string (** CVC5 on the input task. *)
    ; subgoals : int
    ; mode1 : mode list (** r := G, per subgoal. *)
    ; mode2 : mode list (** r := ⊥, per subgoal. *)
    ; dns : int (** bind/sko steps in the proofs used. *)
    ; lost : string option
    (** Why CVC5 proved the input but not some subgoal. *)
    ; mono : string list (** Type variables made abstract types. *) }

  let not_not_elim f = str Term.(t_implies (t_not (t_not f)) f)

  (** [subgoal name ds orig goal i sg] runs CVC5 on the subgoal [sg] and
      returns its two modes, its number of bind/sko steps, and CVC5's answer
      if it is not a proof. [orig] is the proof info of the input task, if
      CVC5 proved it. *)
  let subgoal name ds orig goal i (sg : Morley.subgoal) =
    Pretty.forget_all ();
    say "-- subgoal %d: %a@." (i + 1) term sg.concl;
    let inst f = Morley.instance sg.preds f in
    List.iter (fun (r, (ys, phi)) ->
        say "   %a := %a@." term Term.(ps_app r (List.map t_var ys))
          term phi) sg.preds;
    List.iter (fun (n, (k : Morley.kind), f) ->
        match k with
        | Hyp h -> say "   %-8s %a   (from %s)@." n term f h
        | Def -> say "   %-8s %a@." n term f
        | Tot_em | Tot_all ->
            say "   %-8s %a   [instance: %a]@." n term f term (inst f))
      sg.axioms;
    say "   goal     %a@." term sg.goal;
    List.iter (fun (n, _, f) ->
        if not (Morley.geometric f) then
          say "   BUG: %s is not a geometric implication@." n)
      sg.axioms;
    if not (Morley.coherent sg.goal) then say "   BUG: goal not coherent@.";
    let task = Morley.task_of_subgoal ds sg in
    let smt = Cvc5.smtlib task in
    match Cvc5.answer (Cvc5.run (Printf.sprintf "%s.%d" name (i + 1)) smt) with
    | Cvc5.Other s ->
        say "   CVC5: %s@." s;
        let mode2, dns =
          match orig with
          | None -> None, 0
          | Some info ->
              say "   r := ⊥ falls back on the proof of the input task@.";
              Some (if Morley.stable goal then [] else [not_not_elim goal]),
              dns info
        in
        None, mode2, dns, Some s
    | Cvc5.Unsat cmds ->
        let info = Cvc5.analyse smt cmds in
        say "   CVC5: unsat; uses %s@." (String.concat " " info.used);
        say "   rules: @[%a@]@." rules info;
        if info.unmatched > 0 then
          say "   WARNING: %d used assumptions match no assertion@."
            info.unmatched;
        let used k =
          List.filter (fun (n, k', _) -> k = k' && List.mem n info.used)
            sg.axioms
        in
        let tot_em = used Morley.Tot_em and tot_all = used Morley.Tot_all in
        let mode1 = List.map (fun (_, _, f) -> str (inst f)) (tot_em @ tot_all)
        and mode2 =
          List.map (fun (_, _, f) -> str Term.(t_not (t_not (inst f)))) tot_all
          @ (if Morley.stable sg.concl then [] else [not_not_elim sg.concl])
        in
        Some mode1, Some mode2, dns info, None

  let pp_mode ppf = function
    | None -> Format.fprintf ppf "no proof"
    | Some [] -> Format.fprintf ppf "no EM"
    | Some l ->
        Format.fprintf ppf "leftovers: @[<v>%a@]"
          (Format.pp_print_list Format.pp_print_string) l

  let problem ({Problems.file; name; task} : Problems.problem) : row =
    say "@.==== %s: %s ====@." file name;
    let row = { file; name; classical = ""; subgoals = 0; mode1 = []
              ; mode2 = []; dns = 0; lost = None; mono = [] } in
    match task with
    | Error msg ->
        say "not translated: %s@." msg;
        { row with classical = "not translated" }
    | Ok task ->
        Pretty.forget_all ();
        let task, mono = Mono.monomorphise task in
        if mono <> [] then
          say "   type variables made abstract types: %s@."
            (String.concat " " mono);
        let run = file ^ "." ^ name in
        let ds, hyps, goal = Morley.split_task task in
        List.iter (fun (h, f) -> say "   %-8s %a@." h term f) hyps;
        say "   goal     %a@." term goal;
        let smt = Cvc5.smtlib task in
        let orig, classical =
          match Cvc5.answer (Cvc5.run (run ^ ".input") smt) with
          | Cvc5.Unsat cmds ->
              let info = Cvc5.analyse smt cmds in
              say "   CVC5 on the input: unsat; rules: @[%a@]@." rules info;
              Some info, "unsat"
          | Cvc5.Other s -> say "   CVC5 on the input: %s@." s; None, s
        in
        let subgoals = Morley.transform hyps goal in
        let results = List.mapi (subgoal run ds orig goal) subgoals in
        List.iteri (fun i (m1, m2, _, _) ->
            say "   subgoal %d, r := G: %a@." (i + 1) pp_mode m1;
            say "   subgoal %d, r := ⊥: %a@." (i + 1) pp_mode m2)
          results;
        let mode1 = List.map (fun (m, _, _, _) -> m) results
        and mode2 = List.map (fun (_, m, _, _) -> m) results in
        { row with
          classical; subgoals = List.length subgoals; mode1; mode2; mono
        ; dns = List.fold_left (fun n (_, _, d, _) -> n + d) 0 results
        ; lost =
            if orig = None then None
            else List.find_map (fun (_, _, _, fail) -> fail) results }

  (** Summary of a mode over all subgoals. *)
  let summary (ms : mode list) : string =
    if ms = [] then "-"
    else if List.mem None ms then "no proof"
    else
      match List.concat_map Option.get ms with
      | [] -> "no EM"
      | l -> Printf.sprintf "%d leftover%s" (List.length l)
               (if List.length l > 1 then "s" else "")

  (** A problem is solved without EM if every subgoal has a mode without
      leftovers. *)
  let em_free (r : row) : string =
    let free = function Some [] -> true | _ -> false in
    let both = List.combine r.mode1 r.mode2 in
    if both = [] then "-"
    else if List.for_all (fun (m, _) -> free m) both then "yes (r := G)"
    else if List.for_all (fun (m1, m2) -> free m1 || free m2) both then
      "yes (r := G or ⊥)"
    else "no"

  let table (rows : row list) : unit =
    Format.printf "@.%-12s %-14s %-4s %-14s %-14s %-8s %s@." "problem"
      "CVC5 on input" "sub" "r := G" "r := ⊥" "bind/sko" "without EM";
    List.iteri (fun i r ->
        if i = 0 || (List.nth rows (i - 1)).file <> r.file then
          Format.printf "-- %s@." r.file;
        Format.printf "%-12s %-14s %-4d %-14s %-14s %-8d %s%s%s@." r.name
          r.classical r.subgoals (summary r.mode1) (summary r.mode2) r.dns
          (em_free r)
          (match r.lost with Some s -> "  LOST: " ^ s | None -> "")
          (if r.mono = [] then ""
           else "  (abstract types: " ^ String.concat " " r.mono ^ ")"))
      rows
end

let () =
  let files = ref [] in
  let spec =
    Arg.align
      [ "--driver", Arg.Set_string Cvc5.driver_file,
        "FILE Why3 driver that prints the SMT-LIB problem (default \
         cvc5.drv; tests/constructionism/raw_cvc5.drv has no \
         transformations)"
      ; "--cvc5-options", Arg.Set_string Cvc5.extra_options,
        "OPTS extra CVC5 options, e.g. --enum-inst"
      ; "--timeout", Arg.Set_int Cvc5.timeout,
        "SEC time limit of each CVC5 call (default 10)"
      ; "--out", Arg.String (fun d -> Cvc5.out_dir := Some d),
        "DIR keep the SMT-LIB problems and CVC5 outputs in DIR"
      ; "--quiet", Arg.Set Report.quiet, " print the summary table only" ]
  in
  Arg.parse spec (fun f -> files := f :: !files)
    "constructionism_why3_test [options] FILE.lp ...";
  Common.Library.set_lib_root (Some (Sys.getcwd ()));
  try
    let problems = List.concat_map Problems.load (List.rev !files) in
    Report.table (List.map Report.problem problems)
  with Common.Error.Fatal (pos, msg, _) ->
    Format.eprintf "%a: %s@." Common.Pos.pp (Option.join pos) msg;
    exit 1
