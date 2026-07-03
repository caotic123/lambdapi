(** E-graph coordinator: bridges the core hooks ({!Core.Infer.infer_hook},
    {!Core.Eval.conv_hook}) to {!Egraph}.  RECORDS typing facts during checking,
    REPLAYS the ground ones after each command (relate + fire [when]s), and
    CONSULTS the graph when structural conversion fails.  Gated by [LP_EGRAPH=1]
    (off ⇒ hooks not installed, zero overhead); one process-wide graph is sound
    within a run because variable uids never recur.  Known limits: the graph is
    monotonic (no scoping/rollback), and flush/consult costs are experiment-grade
    (full symbol rescans, permanent query interning). *)

open Lplib
open Core
open Term

(** Feature gate.  Off unless [LP_EGRAPH] is [1]/[true] in the environment. *)
let enabled : bool =
  match Sys.getenv_opt "LP_EGRAPH" with Some ("1" | "true") -> true | _ -> false

(** Display gate.  With [LP_EGRAPH_PRINT=1] (and the feature on), every interned
    term is registered and, after each command that changed the graph, the
    equivalence classes are printed — each class a ruled block headed by its
    shortest member, typing facts appearing as [τ(t)] members.
    [LP_EGRAPH_PRINT=all] shows the WHOLE graph, singleton classes included. *)
let print_enabled : bool =
  enabled
  && match Sys.getenv_opt "LP_EGRAPH_PRINT" with
     | Some ("1" | "true" | "all") -> true | _ -> false

(** Whether the display includes singleton classes ([LP_EGRAPH_PRINT=all]). *)
let print_all : bool =
  Sys.getenv_opt "LP_EGRAPH_PRINT" = Some "all"

(** The process-wide e-graph. *)
let graph : Egraph.t = Egraph.create ()

(** Subterm facts [(ctxt, term, type)] recorded during the current command's
    inference, newest first.  A plain [Stdlib] ref (NOT [Timed]) so it is not
    rolled back by unification backtracking. *)
let buffer : (ctxt * term * term) list ref = ref []

(** Buffer size + hard cap: drivers that never {!flush} (LSP, [Pure]) must not
    accumulate unboundedly; beyond the cap we stop recording (safe to drop). *)
let buffer_len = ref 0
let max_buffer = 100_000

(** Re-entrancy latch: nested {!Eval.conv_hook} entries answer [false] and
    {!record} stays quiet while consulting. *)
let in_consult : bool ref = ref false

(** Qualified names of symbols already interned (intern each declaration once). *)
let seen : Extra.StrSet.t ref = ref Extra.StrSet.empty

(** Recorder installed as {!Core.Infer.infer_hook}: stash references only —
    metas resolve in place, so a post-solve replay sees ground forms. *)
let record : ctxt -> term -> term -> unit =
  fun c t ty ->
  if not !in_consult && !buffer_len < max_buffer then begin
    incr buffer_len; buffer := (c, t, ty) :: !buffer
  end

let () = if enabled then Infer.infer_hook := record
let () = if print_enabled then Egraph.trace := true

(** Groundness (shared with {!Egraph.fire}): holes must not enter the graph. *)
let is_ground : term -> bool = Egraph.is_ground

(** [when] constraints seen at the last {!flush}, for mid-command firing. *)
let known_constraints : constr_rule list ref = ref []

(** Record [type(tm) = ty] and fire every matching constraint; returns #fires. *)
let relate_and_fire ctx tm ty constraints =
  Egraph.relate_type graph ctx tm ty;
  List.fold_left
    (fun n cr -> if Egraph.fire graph ctx cr ~subj:tm ~ty then n + 1 else n)
    0 constraints

(** [replay_ground ()] drains the GROUND buffered facts into the graph (relate +
    fire), keeping non-ground ones (their metas may still get solved); rebuilds if
    anything was replayed.  Closes the within-command timing gap: a conversion can
    use facts recorded earlier in the SAME command. *)
let replay_ground : unit -> int * int = fun () ->
  if !buffer = [] then (0, 0)
  else begin
    let ground, rest =
      List.partition (fun (_, t, ty) -> is_ground t && is_ground ty) !buffer in
    if ground = [] then (0, 0)
    else begin
      buffer := rest; buffer_len := List.length rest;
      let n_fire =
        List.fold_left
          (fun n (c, t, ty) -> n + relate_and_fire c t ty !known_constraints)
          0 (List.rev ground)
      in
      Egraph.rebuild graph;
      (List.length ground, n_fire)
    end
  end

(** [consult ctx a b]: are [a] and [b] equal modulo the e-graph's equations?  The
    structural-conversion FALLBACK installed as {!Eval.conv_hook} (thus reached
    only AFTER structural conversion failed).  Flat, no recursion: replay the
    pending ground facts, SATURATE both terms ({!Egraph.saturate} fires the
    [when] constraints on every typed subterm, INSIDE binders, with equations
    keyed at each occurrence's env), then ask for a single class equality —
    CONGRUENCE propagates the merged bodies up through binders and application
    heads, so nested positions need no explicit descent.
    No-op ([false]) unless {!enabled}. *)
let consult : ctxt -> term -> term -> bool =
  fun ctx a b ->
  (* An interning error (e.g. a residual hole reaching [of_term]) must not abort
     the check: a failed consult just means "cannot decide", i.e. [false].  But
     asynchronous exceptions (Ctrl-C, stack/memory exhaustion) are re-raised —
     swallowing them would mask the real failure as "not convertible". *)
  (* GATE on constraints existing: with no [when] in scope the graph holds only
     bare typing relations — structural conversion already decided these terms,
     so consulting can add nothing.  Crucially this also keeps the e-graph INERT
     on when-less files whose rewrite systems do not normalize (the stock KO
     suite!): [intern]'s Eval.snf would diverge where eq_modulo's lazy whnf
     fails fast. *)
  enabled && !known_constraints <> [] && not !in_consult
  && begin
    in_consult := true;
    Fun.protect ~finally:(fun () -> in_consult := false) @@ fun () ->
    try
      ignore (replay_ground ());
      Egraph.saturate graph ctx !known_constraints a;
      Egraph.saturate graph ctx !known_constraints b;
      Egraph.rebuild graph;
      Egraph.equiv_terms graph ctx a b
    with
    | Stack_overflow | Out_of_memory | Sys.Break as e -> raise e
    | _ -> false
  end

(* Consult the e-graph from the type-checker's conversion (checking + unification),
   not just from asserts.  Only when structural [eq_modulo] already failed, so it
   can only make MORE things convertible — the cubical path/η equations. *)
let () = if enabled then Eval.conv_hook := consult

(** [discharge p] drops from [p]'s UNSOLVED constraints those the e-graph
    decides.  The unifier parks some conversion goals through paths that never
    consult (e.g. [Unif.inverse]'s fallback), so endpoint conversions like
    [t ≡ p ⋅ i0] arising while CHECKING A TYPE would otherwise surface as
    "the proof is not finished".  Call after solving, before turning leftovers
    into goals.  No-op unless {!enabled}. *)
let discharge : problem -> unit = fun p ->
  if enabled then
    Timed.(p :=
      { !p with
        unsolved =
          List.filter
            (fun (c, a, b) ->
               let ok = consult c a b in
               if ok && print_enabled then
                 Format.eprintf "[egraph] discharged %a ≡ %a@."
                   Print.term a Print.term b;
               not ok)
            !p.unsolved })

(** [flush sign]: replay this command's facts into the e-graph — first any
    newly-declared symbols (so constraints fire on declarations like
    [p : Path A t u], whose fact is not an inference result), then the buffered
    subterm facts ({!replay_ground}: ground ones only; non-ground are dropped
    here since the command is over), then {!Egraph.rebuild}.
    Call AFTER each command (i.e. post-solve).  No-op unless {!enabled}. *)
let flush : Sign.t -> unit = fun sign ->
  if not enabled then () else begin
    let constraints = Timed.(!(sign.sign_constraints)) in
    known_constraints := constraints;
    (* Same gate as [consult]: no [when]s ⇒ nothing to fire, so do not pay (or
       risk — Eval.snf may diverge on non-normalizing rule sets) the interning
       of every symbol and fact.  Just drop the buffer. *)
    if constraints = [] then begin buffer := []; buffer_len := 0 end
    else begin
    let n_rel = ref 0 and n_fire = ref 0 in
    (* (1) newly-declared symbols: intern (s : sym_type) once each. *)
    Extra.StrMap.iter
      (fun _ (s : sym) ->
         let key = String.concat "." (s.sym_path @ [s.sym_name]) in
         if not (Extra.StrSet.mem key !seen) then begin
           seen := Extra.StrSet.add key !seen;
           let ty = Timed.(!(s.sym_type)) in
           if is_ground ty then begin
             incr n_rel;
             n_fire := !n_fire + relate_and_fire [] (mk_Symb s) ty constraints
           end
         end)
      Timed.(!(sign.sign_symbols));
    (* (2) buffered subterm facts from this command's inference. *)
    let (r, f) = replay_ground () in
    n_rel := !n_rel + r; n_fire := !n_fire + f;
    (* the command is over: whatever is still non-ground never became so. *)
    buffer := []; buffer_len := 0;
    Egraph.rebuild graph;
    if !n_rel > 0 || !n_fire > 0 then begin
      Printf.eprintf "[egraph] %d type-relations, %d constraint-fires\n%!"
        !n_rel !n_fire;
      if print_enabled then
        Format.eprintf "%a@?" (Egraph.pp_classes ~all:print_all) graph
    end
    end
  end
