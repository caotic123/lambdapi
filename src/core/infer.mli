(** Type inference and checking *)

open Term

(** Hook fired at every [infer] result as [hook ctxt term inferred_type] (no-op by
    default).  Installed by the e-graph coordinator to RECORD typing facts; kept
    here to invert the dependency (core must not depend on the e-graph library).
    A [Stdlib.ref] so installing it survives unification backtracking — the
    installed recorder must only stash references (metas resolve in place). *)
val infer_hook : (ctxt -> term -> term -> unit) Stdlib.ref

(** [infer_noexn p ctx t] returns [Some(t',a)] where [t'] is a refinement of
   [t] and [a] is some type for [t'] in the context [ctx], and [None]
   otherwise, possibly adding new constraints in [p]. The metavariables of [p]
   are updated when a metavariable is instantiated or created. [ctx] must be
   well sorted. *)
val infer_noexn : problem -> ctxt -> term -> (term * term) option

(** [check_noexn p ctx t a] returns [Some t'] if [t] can be refined to [t'] of
   type [a] in context [ctx], and [None] otherwise, possibly adding new
   constraints in [p]. The metavariables of [p] are updated when a
   metavariable is instantiated or created. The context [ctx] and the type [a]
   must be well sorted. *)
val check_noexn : problem -> ctxt -> term -> term -> term option

val check_sort_noexn : problem -> ctxt -> term -> (term * term) option
