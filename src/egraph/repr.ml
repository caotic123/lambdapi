(** E-graph LANGUAGE for Lambdapi terms: the node [shape] ego is instantiated
    with (a first-order mirror of {!type:Core.Term.term}; the S-prefix avoids
    constructor collisions under [open Term]) and the translation {!of_term}.
    The graph instance and the [when]-firing live in {!Egraph}. *)

open Core
open Term

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

(** An e-node: an operator applied to children (e-class ids ['a]).  [SPatt]
    appears only in constraint equations, never in ground subjects; [Bvar]/
    [TRef]/[Wild]/[Plac] have no shape and are eliminated before interning. *)
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

(** Concrete node trees (ego's [LANGUAGE.t]). *)
type t = Mk of t shape [@@unboxed]

(* Structural ops required by ego's [LANGUAGE] functor. *)

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

(** [of_term env t] translates [t] into a node tree.  Matches on [unfold t]
    (skips [TRef]/solved metas); bound variables are keyed by de Bruijn INDEX
    so α-equivalent binders — and the same closed subterm at any depth —
    intern identically (both required for congruence). *)

type env = {
  depth : int;          (** binders entered so far *)
  lvl   : int VarMap.t; (** bound var ↦ the level (env.depth) at its binder *)
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
