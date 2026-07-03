(** {1 E-graph representation of Lambdapi terms — bridge to the [ego] library.}

    PURPOSE.  The SATURATING fragment of the [when] mechanism — the additional
    type constraints whose equations are non-orientable and mutually triggering
    (path-η as a merge, overlap-agreement; cf. [sketch_simple.context] and the
    design notes in [src/core/eval.ml:134-174]) — needs an equivalence-class
    structure, not just rewriting.  We host it on [ego] (OCaml e-graphs).

    This module is the BRIDGE.  It defines:
      - {!type:shape}, the e-graph LANGUAGE (the node "shape" ego is instantiated
        with), as a first-order-ised mirror of {!type:Core.Term.term} — the
        S-prefix on constructors avoids collisions with [Term]'s under
        [open Term]; and
      - {!val:of_term}, the translation [term -> Repr.t node tree] (interned by
        {!Egraph.add}).

    SCOPE: term <-> node only.  The graph instance, the [when] firing, and the
    hooks into inference/conversion live in {!Egraph} / [Handle.Eg_coord].

    DESIGN RECAP (why the translation looks the way it does):
      - GROUND congruence closure: descending under a binder, the bound variable
        is SKOLEMIZED to a fresh constant keyed by its de Bruijn INDEX, so that
        α-equivalent binders intern to the SAME node — and the same closed subterm
        interns identically at any depth (both necessary for congruence).
      - Guards/endpoints come from TYPES (typed-conversion-on-trigger,
        eval.ml:112-125), so every equation entering the graph is ground/closed.
*)

open Core
open Term

(** E-class ids are [Ego.Id.t]; they live in {!module:Egraph}, which instantiates
    ego's [Generic.Make] over THIS module (used as the [LANGUAGE]).  Here we stay
    pure: the term LANGUAGE — [shape] / [op] / [t] — plus [of_term]. *)

(* ───────────────────────────────────────────────────────────────────────── *)
(** {2 Keys — stable identities for leaf nodes.} *)
type sym_key = string

type meta_key = int

(** Operator tags — ego's [LANGUAGE.op]: one per {!shape} arm, carrying the LEAF
    PAYLOAD (the string/int that is NOT a child) so that [op] + children fully
    determine a node.  [SApp]/[SProd]/… carry no payload, only children. *)
type op =
  | OType | OKind
  | OSym  of string
  | OVar  of string
  | OApp | OProd | OAbst | OLet
  | OMeta of meta_key
  | OPatt of int

(* ───────────────────────────────────────────────────────────────────────── *)
(** {2 The e-graph LANGUAGE — the node "shape".}

    An e-node is an operator applied to CHILDREN, each child being an e-class id.
    Following egg/ego, the shape is parameterised by the child type ['a] (= {!id}
    in the live graph).  This is the type ego's [LANGUAGE] functor is built over.

    Constructors are S-PREFIXED so they don't collide with {!module:Core.Term}'s
    constructors (which are in scope via [open Term]).

    CASES (a first-order mirror of {!type:Core.Term.term}):
    {ul
     {- [SType], [SKind]      — sort leaves (Term.Type / Term.Kind).}
     {- [SSym k]              — a symbol head, a 0-ary leaf (Term.Symb).
                                Arguments arrive via [SApp], NOT here.}
     {- [SVar k]              — free var / skolem leaf (Term.Vari, and the
                                de Bruijn skolem standing for a Term.Bvar).}
     {- [SApp (f, x)]         — application (Term.Appl).  Spines [f x y] become
                                nested [SApp(SApp(f,x),y)], as in [term].}
     {- [SProd (a, b)]        — Π-type (Term.Prod): [a] domain, [b] BODY interned
                                under a fresh skolem.}
     {- [SAbst (a, b)]        — λ (Term.Abst): same shape as [SProd].}
     {- [SLet (a, t, b)]      — let (Term.LLet): type, definition, body(skolem).}
     {- [SMeta (m, args)]     — metavariable application (Term.Meta).  Carries the
                                §7c fragment: terms under metavariables.}
     {- [SPatt (i, args)]     — SCHEMA / pattern variable (Term.Patt).  Appears
                                ONLY when interning a CONSTRAINT's equations
                                ([cr_eqns]); [i] is the slot bound by guard-match.
                                Unreachable on GROUND subjects.}}

    Term constructors with NO shape (eliminate before interning — see [of_term]):
      - [Bvar]        : consumed by the [Prod]/[Abst]/[Let] descent.
      - [TRef]        : follow the ref via [Term.unfold] first.
      - [Wild],[Plac] : holes; must not reach the ground graph.
*)
type 'a shape =
  | SType
  | SKind
  | SSym  of string
  | SVar  of string
  | SApp  of 'a * 'a
  | SProd of 'a * 'a
  | SAbst of 'a * 'a
  | SLet  of 'a * 'a * 'a
  | SMeta of meta_key * 'a list
  | SPatt of int * 'a list

(** Concrete terms of the LANGUAGE, "tying the knot" (ego's [LANGUAGE.t]).
    [of_term] produces these; [Egraph.intern] feeds them to ego's [add_node]. *)
type t = Mk of t shape [@@unboxed]

(** {3 Structural ops ego's [LANGUAGE] functor expects.}  Provided complete —
    purely mechanical over {!type:shape}.  (Adapt names to your [ego] version.) *)

(** The children (e-class ids) of a node, left to right. *)
let children : 'a shape -> 'a list = function
  | SType | SKind | SSym _ | SVar _ -> []
  | SApp (a, b) | SProd (a, b) | SAbst (a, b) -> [a; b]
  | SLet (a, b, c) -> [a; b; c]
  | SMeta (_, xs) | SPatt (_, xs) -> xs

(** Functorial map over children — used by ego to rebuild a node after its
    children have been canonicalised to new class ids. *)
let map_children : 'a shape -> ('a -> 'b) -> 'b shape = fun sh f ->
  match sh with
  | SType -> SType
  | SKind -> SKind
  | SSym k -> SSym k
  | SVar k -> SVar k
  | SApp  (a, b)    -> SApp  (f a, f b)
  | SProd (a, b)    -> SProd (f a, f b)
  | SAbst (a, b)    -> SAbst (f a, f b)
  | SLet  (a, b, c) -> SLet  (f a, f b, f c)
  | SMeta (m, xs)   -> SMeta (m, List.map f xs)
  | SPatt (i, xs)   -> SPatt (i, List.map f xs)

(** The discriminating tag of a node (ego's [LANGUAGE.op]). *)
let op : 'a shape -> op = function
  | SType -> OType | SKind -> OKind
  | SSym k -> OSym k | SVar k -> OVar k
  | SApp _ -> OApp | SProd _ -> OProd | SAbst _ -> OAbst | SLet _ -> OLet
  | SMeta (m, _) -> OMeta m | SPatt (i, _) -> OPatt i

(** Rebuild a node from a tag + children (ego's [LANGUAGE.make]); inverse of
    [op] ⊗ [children].  Raises on an arity mismatch. *)
let make : op -> 'a list -> 'a shape = fun o args ->
  match o, args with
  | OType, []        -> SType
  | OKind, []        -> SKind
  | OSym k, []       -> SSym k
  | OVar k, []       -> SVar k
  | OApp,  [a; b]    -> SApp  (a, b)
  | OProd, [a; b]    -> SProd (a, b)
  | OAbst, [a; b]    -> SAbst (a, b)
  | OLet,  [a; b; c] -> SLet  (a, b, c)
  | OMeta m, xs      -> SMeta (m, xs)
  | OPatt i, xs      -> SPatt (i, xs)
  | _ -> invalid_arg "Repr.make: arity mismatch"

(** Equality of tags (ego's [LANGUAGE.equal_op]). *)
let equal_op (a : op) (b : op) : bool =
  match a, b with
  | OType, OType | OKind, OKind | OApp, OApp
  | OProd, OProd | OAbst, OAbst | OLet, OLet -> true
  | OSym x, OSym y | OVar x, OVar y -> String.equal x y
  | OMeta m, OMeta n -> Int.equal m n
  | OPatt i, OPatt j -> Int.equal i j
  | _ -> false

(** Total order on nodes (tag, then children via [cmp]).  Needed for ego's
    hash-consing / class table. *)
let compare_shape : ('a -> 'a -> int) -> 'a shape -> 'a shape -> int =
  fun cmp s1 s2 ->
  let rec lcmp xs ys = match xs, ys with
    | [], [] -> 0 | [], _ -> -1 | _, [] -> 1
    | x :: xs, y :: ys -> let r = cmp x y in if r <> 0 then r else lcmp xs ys in
  let tag = function
    | SType -> 0 | SKind -> 1 | SSym _ -> 2 | SVar _ -> 3 | SApp _ -> 4
    | SProd _ -> 5 | SAbst _ -> 6 | SLet _ -> 7 | SMeta _ -> 8 | SPatt _ -> 9 in
  match s1, s2 with
  | SType, SType | SKind, SKind -> 0
  | SSym a, SSym b | SVar a, SVar b -> String.compare a b
  | SApp (a, b), SApp (c, d)
  | SProd (a, b), SProd (c, d)
  | SAbst (a, b), SAbst (c, d) ->
      let r = cmp a c in if r <> 0 then r else cmp b d
  | SLet (a, b, c), SLet (d, e, f) ->
      let r = cmp a d in if r <> 0 then r else
      let r = cmp b e in if r <> 0 then r else cmp c f
  | SMeta (m, xs), SMeta (n, ys) ->
      let r = Int.compare m n in if r <> 0 then r else lcmp xs ys
  | SPatt (i, xs), SPatt (j, ys) ->
      let r = Int.compare i j in if r <> 0 then r else lcmp xs ys
  | _ -> Int.compare (tag s1) (tag s2)

(** Pretty-printer (debugging / dot export). *)
let pp_shape :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a shape -> unit =
  fun pp_child ppf sh ->
  let pl ppf xs =
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ") pp_child ppf xs in
  match sh with
  | SType -> Format.fprintf ppf "Type"
  | SKind -> Format.fprintf ppf "Kind"
  | SSym k -> Format.fprintf ppf "Sym %s" k
  | SVar k -> Format.fprintf ppf "Var %s" k
  | SApp (a, b) -> Format.fprintf ppf "App(%a, %a)" pp_child a pp_child b
  | SProd (a, b) -> Format.fprintf ppf "Prod(%a, %a)" pp_child a pp_child b
  | SAbst (a, b) -> Format.fprintf ppf "Abst(%a, %a)" pp_child a pp_child b
  | SLet (a, b, c) ->
      Format.fprintf ppf "Let(%a, %a, %a)" pp_child a pp_child b pp_child c
  | SMeta (m, xs) -> Format.fprintf ppf "Meta(%d, [%a])" m pl xs
  | SPatt (i, xs) -> Format.fprintf ppf "Patt(%d, [%a])" i pl xs

(* ───────────────────────────────────────────────────────────────────────── *)
(** {2 [of_term] — intern a term into the e-graph.  THE function to implement.}

    Folds a (ground, after skolemization) term into the graph and returns its
    e-class id.  [add] is ego's "insert this node, return its class" primitive
    (e.g. a partial application of [EGraph.add_node]); kept abstract so you bind
    it to your [ego] version.  [env] carries the binder depth for skolem levels.

    Always match on [unfold t], not [t], to transparently skip [TRef],
    instantiated [Meta]s, and [LLet] introduced by evaluation sharing.

    Call as [of_term empty_env t]. Bound variables are keyed by their de Bruijn
    INDEX (depth-relative) so that α-equivalent binders intern identically AND the
    same closed subterm interns identically at any depth — both needed for
    congruence. *)

type env = {
  depth : int;          (** binders entered so far = next de Bruijn LEVEL *)
  lvl   : int VarMap.t; (** bound var ↦ the LEVEL (env.depth) at its binder *)
}

let empty_env : env = { depth = 0; lvl = VarMap.empty }

let rec of_term (env : env) (tm : term) : t =
  match unfold tm with
  | Vari v ->
      (* bound ⇒ key by de Bruijn INDEX (depth-relative ⇒ position-INDEPENDENT:
         the same closed subterm interns identically at ANY binder depth, which
         congruence requires).  [env.lvl] stores the binder's LEVEL; the index at
         this use site is [env.depth - 1 - level].  A genuine free var ⇒ uniq_name. *)
      (match VarMap.find_opt v env.lvl with
       | Some l -> Mk (SVar (Printf.sprintf "#%d" (env.depth - 1 - l)))
       | None   -> Mk (SVar (uniq_name v)))
  | Type -> Mk SType
  | Kind -> Mk SKind
  | Symb s ->
      (* QUALIFIED name (module path + name): bare [sym_name] would make
         same-named symbols from DIFFERENT modules intern to one node, hence
         spuriously congruent.  (Edge case not handled: an escaped name
         containing a literal ['.'] — accepted, as in {!Egraph} [seen] keys.) *)
      Mk (SSym (String.concat "." (s.sym_path @ [s.sym_name])))
  | Appl (a, b) -> Mk (SApp (of_term env a, of_term env b))
  | Prod (a, bnd) ->
      let x, body = unbind bnd in
      let env' = { depth = env.depth + 1; lvl = VarMap.add x env.depth env.lvl } in
      Mk (SProd (of_term env a, of_term env' body))
  | Abst (a, bnd) ->
      let x, body = unbind bnd in
      let env' = { depth = env.depth + 1; lvl = VarMap.add x env.depth env.lvl } in
      Mk (SAbst (of_term env a, of_term env' body))
  | LLet (_a, def, bnd) ->
      (* let-reduction: substitute the definition into the body (transparent),
         so `let x ≔ d in b` interns exactly as `b[d/x]`. *)
      of_term env (subst bnd def)
  | Meta (m, ts) ->
      Mk (SMeta (m.meta_key, List.map (of_term env) (Array.to_list ts)))
  | Patt (io, _n, ts) ->
      (* schema variable (constraint LHS only); None ⇒ anonymous slot, use -1. *)
      let i = match io with Some i -> i | None -> -1 in
      Mk (SPatt (i, List.map (of_term env) (Array.to_list ts)))
  | Bvar _ ->
      (* unreachable: bound vars are consumed by the binder descent above. *)
      assert false
  | TRef _ ->
      (* unreachable after [unfold]. *)
      assert false
  | Wild | Plac _ ->
      (* holes — must not reach the ground e-graph. *)
      failwith "INVALID: Wild/Plac in e-graph term"
   

(* ───────────────────────────────────────────────────────────────────────── *)
(** {2 Reverse direction (sketch only — for reading classes back into terms).}

    Conversion uses the graph to DECIDE [a ≡ b] (same class?), so you mostly
    query, not read back.  If you ever need a witness term from a class, invert
    [of_term]: pick a representative node per class and rebuild, turning
    [Skolem level] back into the binder's bound variable.  Left unimplemented. *)
(* let rec to_term : (id -> id shape) -> id -> term = fun _repr _c ->
     failwith "TODO (optional): rebuild a term from an e-class representative" *)
