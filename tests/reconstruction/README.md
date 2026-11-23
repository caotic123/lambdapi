# Examples for the reconstruction pipeline

The pipeline, with `lambdapi check --experimental-smt-proofs`: the `why3`
tactic sends the goal to CVC5 and gets an Alethe proof;
`carcara translate lambdapi` turns it into a Lambdapi file
(`src/handle/reconstruction.ml`); the file is loaded as a module and
`tac_reconstruct` (`src/handle/tactic.ml`) closes the goal with its
theorem. What relates the theorem to the goal is left as **holes**, which
are admitted (`axiom _axN` warnings). The examples record, for every `why3`
call, how far the pipeline gets and how many holes it leaves.

## Setup

Checked on 2026-11-19. None of these needs to be installed: `run.sh` passes
`--map-dir` options.

| what | version | how |
|---|---|---|
| lambdapi | this branch, OCaml 4.14 | `eval $(opam env --switch=. --set-switch); dune build` |
| CVC5 | 1.3.4-dev | prover `CVC5` of `~/.why3.conf` |
| Carcara | NotBad4U/carcara `lambdapi-refactor`, db66884a | `git worktree add --detach ~/Workspace/carcara-lambdapi alessio/lambdapi-refactor`, then `cargo build --release` there |
| Carcara's library | `alethe-lp/` of the same checkout | its lemma names must match the binary |
| Stdlib | Deducteam/lambdapi-stdlib d1d77a6 (2026-10-30) | `git clone` into `~/Workspace/lambdapi-stdlib` and `git checkout d1d77a6` |

The Stdlib is pinned because 82df3c9 ("remove builtin "0" in Pos",
2026-11-03) needs a newer lambdapi than this branch: with it, `Pos.lp:790`
fails with "ℕ is not unifiable with ℙ".

`run.sh` finds the tools in the places above; set `LAMBDAPI`, `CARCARA_DIR`
(or `CARCARA` and `ALETHE`), `STDLIB` and `OUT` to use other ones (see
`run.sh --help`). Before running, it removes the `.lpo` files of the
libraries and of `tests/OK` that are older than the lambdapi binary (they
"are incompatible with current binary"), then compiles each module of
Carcara's library in its own process, as `alethe-lp/README.md` advises.

## Running

    tests/reconstruction/run.sh                          # every example
    tests/reconstruction/run.sh tests/reconstruction/prop.lp
    tests/reconstruction/run.sh --update                 # accept the outcomes

It prints one line per `why3` call (file, symbol, outcome), the totals, and
the Alethe rules of the translated proofs, then compares the outcomes with
`expected.txt`. It exits with 1 if they differ, and prints the diff. With
`--update` it writes them to `expected.txt` instead (only the lines of the
files that were run). The full logs (`--debug=h`, with each translation) are
in `$OUT/logs`, and each translation is in the `/tmp/lambdapi_carcara_*`
directory that the log names (`proof.alethe`, `problem.smt2`, `proof.lp`,
`reconstruction.lp`).

Outcomes:

| outcome | meaning |
|---|---|
| `reconstructed holes=N` | translated, loaded, and the goal closed with the theorem and `N` admitted holes |
| `… admit=RULE` | Carcara translated the proof only with `--admit-unsupported`: `RULE` has no translation |
| `foreign holes=N` | loaded and applied, but the file's builtins are not those of Carcara's library (logged as `(other builtins)`) |
| `no-translation: MSG` | Carcara failed in both modes; the goal is admitted |
| `not-loaded: MSG` | the translation does not type-check; the goal is admitted |
| `error: MSG` | lambdapi stopped with an error at this call |
| `crash: MSG` | lambdapi stopped with an uncaught exception |
| `not-reached` | an earlier call of the file stopped lambdapi |

The outcomes are read from the warnings of the tactic and from its debug
log (`--debug=h`): `[carc] FILE:L:C translated (MODE) in DIR` and
`[carc] FILE:L:C reconstruction with N holes`. DIR keeps the SMT-LIB
problem, the Alethe proof and Carcara's translation.

A goal is closed with **no** hole when the theorem's constants are all
variables of the goal and the holes for the premises and for the statement
are filled. For `prop.lp`'s `ex1`, the holes can be filled by hand: the
premise holes are `clᵢ₁' h` (for the hypothesis `h` with the same formula)
and the goal hole is `λ h, h` (the statement `π (p_4_ q p)` unfolds to the
goal).

## The examples

| file | what it exercises |
|---|---|
| `prop.lp` | 23 propositional problems, intuitionistic and classical; every constant is a variable of the goal |
| `fol.lp` | sorts, function and predicate symbols, `∀`/`∃` (`forall_inst`, `bind`, `sko_forall`, `qnt_join`) |
| `atoms.lp` | what the tactic does before CVC5: `simplify` of rules and definitions, opaque atoms, the simplification of `cvc5.drv` |
| `encoding.lp` | a goal in the encoding of `tests.OK` instead of the Stdlib |
| `fatal/*.lp` | one call that stops lambdapi each: missing `require`, invalid goal, CVC5 `unknown`, and two crashes of the why3 tactic |

## Outcomes on 2026-11-19

45 calls: 39 reconstructed, 1 foreign, 3 errors and 2 crashes (all in
`fatal/`). `expected.txt` has the details.

- Carcara translates every proof that CVC5 finds, and every translation
  that is loaded type-checks. Only three need `--admit-unsupported`:
  Carcara's Lambdapi backend has no `not_equiv1` (`prop.lp` distrib,
  de_morgan) and no `qnt_join` (`fol.lp` all_swap).
- `prop.lp`: one hole per hypothesis plus one for the goal.
- `fol.lp`, `atoms.lp`: the tactic matches the constants of the problem
  only with the variables of the goal. The global symbols (`nat`, `zero`,
  `succ`, `even`) are holes, and so are the variables whose type mentions
  `nat`, since their type in the translation is over the hole `nat'`. The
  hole `π S → π G` is then not provable, because `S` speaks of the holes.
- `atoms.lp`: the opaque atom `X` is a hole of type `Prop`. In empty_type,
  `cvc5.drv` has turned the goal into `true`, so the hole is `π ⊤ → π G`,
  which needs an element of `τ nat`.
- `encoding.lp`: the translation is applied, but `p` and `q` have type `τ o`
  there and `tests.OK.Prop.Prop` here, so they are holes too.
- `fatal/fun_var.lp`: a variable of type `τ nat → τ nat` makes the why3
  tactic hit `assert false` in `translate_term`. `fatal/poly.lp`: a variable
  `a : Set` makes Why3's printer fail ("polymorphism must be encoded").
- `fatal/ex_all.lp`: CVC5 answers `unknown` without `--enum-inst`.
