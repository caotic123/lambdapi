# Alethe proofs of the tests/why3_examples goals

For each `why3` call in `tests/why3_examples/*.lp`:

- `NAME.smt2`: the SMT-LIB problem Why3 sends to CVC5 for that goal
  (lambdapi's Why3 task after the `cvc5.drv` transformations and the
  `smtv2.6` printer);
- `NAME.alethe`: the Alethe proof CVC5 returns, without CVC5's
  `unsat ( … )` wrapper, so that `parse_alethe.exe` reads it directly.

| NAME | lambdapi symbol | Why3 task (before the driver) | `rare_rewrite` steps |
|---|---|---|---|
| ex1  | `ex1` (`ex1_propositional.lp`, with `begin why3 end`) | `p`, `p -> q` ⊢ `q /\ p \/ not p` | 0 |
| ex2  | `ex2` (`ex2_first_order.lp`)  | `∀n. even n -> even (succ (succ n))`, `even zero` ⊢ `even (succ (succ zero)) /\ (q -> q)` | 2 |
| ex3a | `ex3a` (`ex3_rewrite_rules.lp`) | `even zero` ⊢ `even zero` | 0 |
| ex3b | `ex3b` (`ex3_rewrite_rules.lp`) | `even zero`, `∀n. even n -> even (succ (succ n))` ⊢ `even (succ (succ zero))` | 2 |
| ex4  | `ex4` (`ex4_opaque_atoms.lp`) | `X` ⊢ `X` | 0 |

`ex1_propositional.lp` currently proves `ex1` by hand; its task was taken
from a copy of the same statement proved with `begin why3 end`.

Extra files:

- `ex2.raw.smt2`, `ex2.raw.alethe`: the same goal printed with a driver
  that has no transformations (option B in `AGENTS.md`). It is the only
  example where the two differ: `cvc5.drv` simplifies the goal to
  `even (succ (succ zero))`, the raw driver keeps
  `(and (even (succ (succ zero))) (=> q q))`.
- `ex1.why3-output`: what lambdapi actually receives in `pr_output` for
  ex1. Why3's server sends the prover's stdout and stderr to the same file,
  so the proof comes with CVC5's linker warning (local build) and the
  `--stats-internal` statistics. The parser will have to skip them, or the
  command must drop `--stats-internal`.

## How they were produced (2026-10-29)

Why3 1.8.2 (`_opam`), CVC5 1.3.4-dev (`/usr/local/bin/cvc5`).

1. The Why3 task of each goal was printed with
   `lambdapi check --debug=y` (see `tests/why3_examples/README.md`).
2. The same task was rebuilt with the Why3 OCaml API exactly as
   `Why3_tactic.translate_goal` builds it (from `None`, same names and
   declaration order; the printed tasks are identical), then passed through
   `Driver.prepare_task` and `Driver.print_task_prepared` with `cvc5.drv`.
   This step is needed because CVC5 is not registered in `~/.why3.conf`
   (see `AGENTS.md`), so lambdapi cannot call it yet. Using
   `cvc5_strings_counterexample.drv` (the alternative `Why3_tactic.run`
   would pick) only changes comment lines.
3. Proof, with the options of `Why3_tactic.cvc5_proof_options`:

       cvc5 --dump-proofs --proof-format-mode=alethe --proof-alethe-res-pivots \
            --proof-granularity=dsl-rewrite NAME.smt2

   then the first line (`unsat`), the line `(` and the last line `)` were
   removed.

Check that they parse:

    for f in tests/alethe/why3_examples/*.alethe; do
      dune exec tests/alethe/parse_alethe.exe -- $f > /dev/null && echo "ok $f"; done

## No holes: `--proof-granularity=dsl-rewrite`

Without `--proof-granularity=dsl-rewrite`, ex2, ex3b and ex2.raw contain
`hole` steps (`TRUST_THEORY_REWRITE` of `∀n. (A => B)` into
`∀n. (¬A ∨ B)`). With it, none of the proofs has a `hole`; the rewrite is
justified under the binder instead:

    (anchor :step t1.t3 :args ((n nat) (:= (n nat) n)))
    (step t1.t3.t0 (cl (= (=> (even n) …) (or (not (even n)) …)))
      :rule rare_rewrite :args ("bool-impl-elim" …))
    (step t1.t3 (cl (= (forall ((n nat)) (=> …)) (forall ((n nat)) (or …))))
      :rule bind)

Reconstruction therefore needs one lambdapi lemma per RARE rule used
(`bool-impl-elim` here) and a rule for `bind`.
