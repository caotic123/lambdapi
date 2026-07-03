(** Persistent e-graph over {!Repr} (the term LANGUAGE), backed by [ego]
    ({!Ego.Generic}).

    Lifecycle (driven by [Handle.Eg_coord]):
      - HOLD one instance across the whole run;
      - INTERN typing facts as the IN-GRAPH relation [type(t) = ty]
        ({!relate_type}) and fire the [when] constraints ({!fire});
      - CONSULT it from conversion to decide class-equivalence
        ({!equiv}, {!equiv_terms}).

    The EClass analysis is TRIVIAL (no per-class data): we only need congruence
    closure + manual merges here, not an abstract-interpretation analysis.
    Typing facts live INSIDE the graph as [$type · t] nodes (see
    {!type_of_repr}), not in a side table, so congruence propagates them. *)

open Core

(** Re-export the term LANGUAGE so consumers can build/inspect nodes as
    [Egraph.Repr.*].  (Dune hides sibling modules when the main module name
    matches the library name, so this re-export is needed.) *)
module Repr = Repr

(** Trivial analysis — unit persistent state, unit per-class data. *)
module A = struct
  type t = unit
  type data = unit
  let pp_data fmt () = Format.pp_print_string fmt "()"
  let show_data () = "()"
  let equal_data () () = true
  let default = ()
end

(** Trivial analysis ops — every callback is a no-op over unit data. *)
module MakeOps
    (_ : Ego.Generic.GRAPH_API
         with type 'p t = (Ego.Id.t Repr.shape, A.t, A.data, 'p) Ego.Generic.egraph
          and type analysis := A.t
          and type data := A.data
          and type 'a shape := 'a Repr.shape
          and type node := Repr.t) =
struct
  type 'p t = (Ego.Id.t Repr.shape, A.t, A.data, 'p) Ego.Generic.egraph
  let make _ _ = ()
  let merge () _ _ = ((), (false, false))
  let modify _ _ = ()
end

(** The concrete e-graph over our language [Repr]. *)
module EG = Ego.Generic.Make (Repr) (A) (MakeOps)

(** The held e-graph: just ego's read/write graph.  Typing facts are stored
    INSIDE it as the relation [type(x) = T] (see {!relate_type}), not in a side
    table — so congruence propagates them: [x ≡ y ⟹ type x ≡ type y]. *)
type t = { eg : Ego.Generic.rw EG.t }

(** [create ()] — a fresh empty e-graph; call once per file in [compile.ml]. *)
let create : unit -> t = fun () -> { eg = EG.init () }

(* ─────────────── tracing: a printable registry of interned terms ─────────── *)

(** When [trace] is on (set by [Handle.Eg_coord] from [LP_EGRAPH_PRINT=1]),
    every interned term is recorded together with its e-class id, so the graph
    can be displayed as equivalence classes ({!pp_classes}).  Off by default —
    the registry costs a rendered string per interned term. *)
let trace : bool Stdlib.ref = Stdlib.ref false

let registry : (Ego.Id.t * string) list Stdlib.ref = Stdlib.ref []

let register : Ego.Id.t -> string -> unit = fun id s ->
  if Stdlib.(!trace) then registry := (id, s) :: !registry

(** [add g r] interns a raw {!Repr.t} node and returns its e-class (used to build
    [type(_)] nodes, and in tests). *)
let add : t -> Repr.t -> Ego.Id.t = fun g r -> EG.add_node g.eg r

(** [intern g ctx tm] NORMALISES [tm] (strong nf in context [ctx]) then interns
    it (de Bruijn-level skolemised under binders, via {!Repr.of_term}), returning
    its e-class.  Normalising first collapses reduction-equal terms to ONE node,
    so the e-graph only carries the EXTRA (non-orientable) equations — never what
    the rewriter already decides. *)
let intern_env : t -> Repr.env -> Term.ctxt -> Term.term -> Ego.Id.t =
  fun g env ctx tm ->
  let ntm = Eval.snf ctx tm in
  let id = add g (Repr.of_term env ntm) in
  if Stdlib.(!trace) then
    register id (Format.asprintf "%a" Print.term ntm);
  id

let intern : t -> Term.ctxt -> Term.term -> Ego.Id.t = fun g ctx tm ->
  intern_env g Repr.empty_env ctx tm

(** [type_of_repr r] is the node [$type · r] — "the type of [r]".  ["$type"] is a
    reserved head (no real symbol is named it), so it never collides with a user
    symbol.  (A dedicated [STypeOf] shape constructor would be the collision-proof
    version, if we keep this representation.) *)
let type_of_repr : Repr.t -> Repr.t =
  fun r -> Repr.(Mk (SApp (Mk (SSym "$type"), r)))

(** [relate_type g ctx tm ty] — the "insert a type found" hook, as a REWRITE
    RELATION on types: NORMALISE both [tm] and [ty] (in context [ctx]) and add the
    in-graph equation [type(tm) = ty].  Congruence then carries it for free — if
    [tm ≡ tm'] the e-graph identifies [type tm ≡ type tm'], hence their types. *)
let relate_type : t -> Term.ctxt -> Term.term -> Term.term -> unit =
  fun g ctx tm ty ->
  let ntm   = Eval.snf ctx tm in
  let ctype = add g (type_of_repr (Repr.of_term Repr.empty_env ntm)) in
  if Stdlib.(!trace) then
    register ctype (Format.asprintf "τ(%a)" Print.term ntm);
  let cty   = intern g ctx ty in
  EG.merge g.eg ctype cty

(** [merge g a b] unions two classes; you must {!rebuild} before querying. *)
let merge : t -> Ego.Id.t -> Ego.Id.t -> unit = fun g a b -> EG.merge g.eg a b

(** [rebuild g] restores the congruence invariants after manual {!merge}s. *)
let rebuild : t -> unit = fun g -> EG.rebuild g.eg

(** [equiv g a b] — are classes [a] and [b] congruent?  {!rebuild} first if you
    have merged since the last query. *)
let equiv : t -> Ego.Id.t -> Ego.Id.t -> bool = fun g a b ->
  EG.class_equal (EG.freeze g.eg) a b

(** [equiv_terms g ctx a b] interns [a] and [b] (normalised) and asks whether they
    land in the SAME e-class — i.e. are equal modulo the equations the graph holds
    (path boundary/η …) ON TOP of the rewriter.  Querying only ADDS the two nodes
    (hash-consed onto existing classes), so no {!rebuild} is needed as long as the
    graph was already rebuilt after its last {!merge}. *)
let equiv_terms : t -> Term.ctxt -> Term.term -> Term.term -> bool =
  fun g ctx a b -> equiv g (intern g ctx a) (intern g ctx b)

(** [pp_classes ppf g] displays the graph as its equivalence classes over all
    REGISTERED terms (requires {!trace}; classes with a single distinct member
    are omitted — no equation relates them).  Each class prints as

    {v ──────────────────────────────────────── p
    ipath (λ i, ⋅ p i)
    p v}

    with the shortest member as the headline representative.  Typing facts show
    as [τ(t)] members: a class [τ(p) = PathP …] IS the recorded type constraint
    on [p].  [~all:true] also shows singleton classes (the WHOLE graph); default
    keeps only classes an equation actually relates. *)
let pp_classes : ?all:bool -> Format.formatter -> t -> unit =
  fun ?(all = false) ppf g ->
  let fg = EG.freeze g.eg in
  (* group registered entries by e-class (via class_equal on the frozen graph) *)
  let classes : (Ego.Id.t * string list Stdlib.ref) list Stdlib.ref =
    Stdlib.ref [] in
  List.iter
    (fun (id, s) ->
       match
         List.find_opt (fun (id', _) -> EG.class_equal fg id id') Stdlib.(!classes)
       with
       | Some (_, ms) -> if not (List.mem s Stdlib.(!ms)) then ms := s :: Stdlib.(!ms)
       | None -> classes := (id, Stdlib.ref [s]) :: Stdlib.(!classes))
    (List.rev Stdlib.(!registry));
  let rule = String.concat "" (List.init 44 (fun _ -> "─")) in
  List.iter
    (fun (_, ms) ->
       match Stdlib.(!ms) with
       | [] -> ()
       | [_] when not all -> ()            (* singletons: no equation, skip *)
       | ms ->
           let repr =
             List.hd
               (List.sort
                  (fun a b ->
                     let c = compare (String.length a) (String.length b) in
                     if c <> 0 then c else compare a b) ms) in
           Format.fprintf ppf "%s %s@." rule repr;
           List.iter (Format.fprintf ppf "  %s@.")
             (List.sort compare ms))
    (List.rev Stdlib.(!classes))

(* ─────────────────── firing `when` typed constraints ─────────────────── *)

(** [is_ground t]: after {!Term.unfold} (which resolves SOLVED metas and [TRef]),
    does [t] contain no holes?  A leftover [Meta] is UNSOLVED, a [Plac]/[Wild] an
    unelaborated hole, a [Patt] an uninstantiated schema variable — none may enter
    the graph.  The single groundness predicate shared by the coordinator (fact
    replay) and {!fire} (equation instantiation). *)
let rec is_ground : Term.term -> bool = fun t ->
  let open Term in
  match unfold t with
  | Vari _ | Symb _ | Type | Kind -> true
  | Appl (a, b) -> is_ground a && is_ground b
  | Prod (a, b) | Abst (a, b) ->
      is_ground a && (let _, b = unbind b in is_ground b)
  | LLet (a, d, b) ->
      is_ground a && is_ground d && (let _, b = unbind b in is_ground b)
  | Meta _ | Plac _ | Wild | Patt _ | Bvar _ | TRef _ -> false

(** First-order match of a guard pattern [pat] (schema vars are [Patt(Some i,_,_)])
    against [t], recording bindings in [subs] (slot [i] ↦ matched subterm); a
    repeated variable must be [eq_modulo].  Returns whether it matched.

    Only the first-order spine is handled — enough for type guards like
    [Path a x y] / [PathP H x y], where the schema vars sit at argument
    positions.  A [Patt] occurring UNDER a binder (needing its arguments
    abstracted) is not supported here. *)
let rec match_guard
    (subs : Term.term option array) (pat : Term.term) (t : Term.term) : bool =
  let open Term in
  match unfold pat with
  | Patt (Some i, _, _) ->
      (match subs.(i) with
       | None -> subs.(i) <- Some t; true
       (* repeated var: both bindings are subterms of the SAME already-normalised
          type, so α-equality suffices — and unlike [Eval.eq_modulo] it cannot
          re-enter the conversion hook (hence this graph) mid-fire. *)
       | Some t' -> LibTerm.eq_alpha t t')
  | Patt (None, _, _) -> true                       (* wildcard *)
  | Symb s -> (match unfold t with Symb s' -> s == s' | _ -> false)
  | Vari x -> (match unfold t with Vari y -> eq_vars x y | _ -> false)
  | Type   -> (match unfold t with Type -> true | _ -> false)
  | Kind   -> (match unfold t with Kind -> true | _ -> false)
  | Appl (a, b) ->
      (match unfold t with
       | Appl (c, d) -> match_guard subs a c && match_guard subs b d
       | _ -> false)
  | Prod (a, b) ->
      (match unfold t with
       | Prod (c, d) ->
           let _, b, d = unbind2 b d in
           match_guard subs a c && match_guard subs b d
       | _ -> false)
  | Abst (a, b) ->
      (match unfold t with
       | Abst (c, d) ->
           let _, b, d = unbind2 b d in
           match_guard subs a c && match_guard subs b d
       | _ -> false)
  | _ -> false

(** [fire ?env g ctx cr ~subj ~ty]: if subject [subj]'s type [ty] matches the
    guard [cr.cr_type] (with [subj] bound at slot [cr.cr_subj]), instantiate
    every equation of [cr.cr_eqns] and MERGE its two sides — interned at [env]
    (default empty), so equations fired UNDER A BINDER key the bound variables
    exactly as the surrounding term's occurrences do.  Returns whether it fired.
    Does NOT {!rebuild} — fire your batch, then rebuild once. *)
let fire :
  ?env:Repr.env ->
  t -> Term.ctxt -> Term.constr_rule -> subj:Term.term -> ty:Term.term -> bool =
  fun ?(env = Repr.empty_env) g ctx cr ~subj ~ty ->
  let open Term in
  (* normalise the subject's type so the guard head matches: a user type like
     [Path A t u] only becomes [PathP (λ_,A) t u] after rewriting. *)
  let ty = Eval.snf ctx ty in
  let subs = Array.make cr.cr_vars_nb None in
  subs.(cr.cr_subj) <- Some subj;
  if not (match_guard subs cr.cr_type ty) then false
  else begin
    (* turn the slot bindings into the [mbinder option array] [subst_patt] wants *)
    let penv = Array.map (Option.map (bind_mvar [||])) subs in
    (* An equation may only mention schema vars bound by the guard or the subject;
       if one is unbound, [subst_patt] leaves a [Patt] (or raises) — SKIP that
       equation rather than merge an uninstantiated pattern node.  [is_ground]
       also rejects residual holes ([Plac]/[Wild]/[Meta]) that [intern] cannot
       represent.  Asynchronous exceptions are never swallowed. *)
    let reraise e =
      match e with
      | Stack_overflow | Out_of_memory | Sys.Break -> raise e
      | _ -> ()
    in
    List.iter
      (fun (l, r) ->
         match
           (try Some (subst_patt penv l, subst_patt penv r)
            with e -> reraise e; None)
         with
         | Some (l, r) when is_ground l && is_ground r ->
             (try EG.merge g.eg (intern_env g env ctx l) (intern_env g env ctx r)
              with e -> reraise e)
         | _ -> ())
      cr.cr_eqns;
    true
  end

  

(** [fire_all g ctx crs ~subj ~ty] fires every constraint whose guard matches the
    subject's type.  Pair with {!rebuild} afterwards. *)
let fire_all :
  t -> Term.ctxt -> Term.constr_rule list -> subj:Term.term -> ty:Term.term -> unit
  = fun g ctx crs ~subj ~ty ->
  List.iter (fun cr -> ignore (fire g ctx cr ~subj ~ty)) crs

(** [saturate g ctx crs tm] — the e-graph "lives inside the binders": walk the
    (normalised) term and, at EVERY subterm whose type is cheaply synthesizable
    (bound variables — read from the binder domain — and neutral application
    spines — head's declared type with the arguments substituted through the
    Π's), fire the [when] constraints, interning the equations AT THAT POINT'S
    env.  So under [λ x] with [h x : Path A x x], the boundary equation
    [h x ⋅ i0 ≡ x] enters the graph keyed on [x]'s de Bruijn index — and pure
    CONGRUENCE then decides e.g. [P (λ x, h x ⋅ i0) ≡ P (λ x, x)] with a single
    class query: the bodies collapse, so the [λ]s collapse, so the [P …]s do.
    No type inference machinery: heads whose type isn't declared are skipped. *)
let saturate : t -> Term.ctxt -> Term.constr_rule list -> Term.term -> unit =
  fun g ctx crs tm ->
  if crs = [] then () else
  let open Term in
  (* [ret_ty ty args]: the type of [h a1..an] given [h : ty], by substituting
     the arguments through the products of [ty]. *)
  let rec ret_ty ty args =
    match args with
    | [] -> Some ty
    | a :: rest ->
        (match Eval.whnf ctx ty with
         | Prod (_, b) -> ret_ty (subst b a) rest
         | _ -> None)
  in
  let rec walk (env : Repr.env) (types : term VarMap.t) t =
    match unfold t with
    | Abst (a, b) | Prod (a, b) ->
        walk env types a;
        let x, body = unbind b in
        let env' =
          Repr.{ depth = env.depth + 1; lvl = VarMap.add x env.depth env.lvl }
        in
        walk env' (VarMap.add x a types) body
    | LLet (_, d, b) -> walk env types (subst b d)
    | _ ->
        let h, args = get_args t in
        List.iter (walk env types) args;
        let hty =
          match unfold h with
          | Symb s -> Some Timed.(!(s.sym_type))
          | Vari x ->
              (match VarMap.find_opt x types with
               | Some a -> Some a
               | None ->
                   (try Some (Ctxt.type_of x ctx) with Not_found -> None))
          | _ -> None
        in
        (match Option.bind hty (fun ty -> ret_ty ty args) with
         | Some ty ->
             List.iter (fun cr -> ignore (fire ~env g ctx cr ~subj:t ~ty)) crs
         | None -> ())
  in
  walk Repr.empty_env VarMap.empty (Eval.snf ctx tm)
