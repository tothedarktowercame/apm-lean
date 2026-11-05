# apm-lean: University of Texas prelim problems in Lean 4

This repository formalises, in Lean 4 with Mathlib, the problems from the
University of Texas at Austin mathematics preliminary examinations (1990s to
2003).

Each problem has a Lean statement, and all but a few have a Lean proof. A problem counts as
**closed** when its `problems/P/lean/Main.lean` compiles with no `sorry`, and
the theorem it proves matches an entry in the statement registry
(`problems/STATEMENTS.json`). An entry goes into the registry only after an
outside grader has compared the Lean statement with the problem text.

## Where things stand (2026-11-05)

| | count |
|---|---|
| problems | 480 |
| closed: `Main.lean` has no `sorry` | 462 |
| open | 18, all topology (`t*`) |
| registered statements | 479 (437 graded faithful, 26 stronger, 16 narrower) |

A "narrower" statement is admitted only where the problem text itself is
defective (for instance a claim that is false as printed); the defect is
written up beside the problem. One closed problem (`a97A07`) has no registered
statement yet.

These numbers come from `problems/*/status.json` and
`problems/STATEMENTS.json`; recompute them rather than trusting this table.

## The 18 open problems: contributions welcome

All remaining problems are in algebraic and differential topology, where
Mathlib's coverage is thinnest. Each one is worth solving on its own terms, and
each would add reusable topology to Lean.

| problem | subject | state |
|---|---|---|
| `t00A03` | simple essential curves on a closed surface of genus ≥ 2 | blueprint, 2 leaves open |
| `t00J05` | 2-complex from a torus with a disk attached along an essential curve | blueprint, 5 leaves open |
| `t01A05` | degree of orientation-preserving k-sheeted coverings of manifolds | `Main.lean`, 1 `sorry` |
| `t01J01` | null-homologous curves on a genus-2 surface bound a subsurface | blueprint, 2 leaves open |
| `t01J05` | partitions of unity; nowhere-zero 1-forms on compact manifolds | blueprint, 1 leaf open |
| `t02A08` | maps S² → S¹×S² with every intersection number n | `Main.lean`, 2 `sorry` |
| `t03J01` | retractions of the double torus onto separating/non-separating curves | blueprint, 2 leaves open |
| `t03J03` | 2-fold covers of the connected sum of three projective planes | blueprint, 2 leaves open |
| `t03J05` | intersection numbers of embedded tori in F × F, F of genus 2 | blueprint, 2 leaves open |
| `t91A01` | vector fields on surfaces: index of isolated zeros | blueprint, 1 leaf open |
| `t94J07` | homotopic maps have equal integrals of closed forms | `Main.lean`, 1 `sorry` |
| `t96J06` | RP¹×RP¹ does not bound in RP²×RP² (intersection theory) | blueprint, 1 leaf open |
| `t97A05` | intersection numbers of nested oriented submanifolds | blueprint, 1 leaf open |
| `t97A06` | Poincaré dual forms of compact oriented submanifolds | blueprint, 2 leaves open |
| `t97J02` | 5- and 6-fold covers of the connected sum of four projective planes | blueprint, 5 leaves open |
| `t98A06` | lifting vector fields through submersions; flows | blueprint, 2 leaves open |
| `t99A04` | separating vs non-separating embedded circles in a surface | `Main.lean`, 1 `sorry` |
| `t99J03` | classification of compact triangulated surfaces | blueprint, 1 leaf open |

"Blueprint" means `holes/labs/blueprints/P/`: `Blueprint.lean` reduces the
problem to named lemmas ("leaves") and `BLUEPRINT.md` sketches a proof of each
one. A leaf is the best place to start: it is a single Lean theorem whose
body is `sorry`, its statement is fixed, and the sketch names the Mathlib
results to use.

### How to contribute a proof

1. Install the toolchain in `lean-toolchain` (Lean `v4.29.0-rc8`); Mathlib is
   pinned in `lake-manifest.json`. Run `lake exe cache get`, then build what
   you need with `lake env lean <file>`.
2. Pick a problem or a leaf. Read `problems/P/problem.md` (the problem as set),
   `problems/P/informal-solution.md`, and the blueprint if there is one.
3. Prove it without changing the statement. The registered theorem and every
   definition it reaches are fingerprinted:
   `python3 scripts/statement-registry.py check P` must still report a match.
   If you believe a statement is wrong (false, or not what the problem asks),
   open an issue with the counterexample instead: statement repairs go through
   the registry and an outside grade.
4. Check `#print axioms` on the theorem: only `propext`, `Classical.choice` and
   `Quot.sound`. `sorry`, new `axiom`s and `native_decide` are not accepted.
5. Open a pull request with the proof and the compile output. A proved leaf is
   a welcome contribution even if the problem stays open.

Proofs of general facts (covering-space classification, surface
classification, Poincaré duality on manifolds, intersection theory) are
welcome in `ConstructionTargets/`, the shared library; see
[`methods/04-library.md`](methods/04-library.md).

## How the proofs were made

The proofs were written by AI agents (mostly OpenAI Codex and Anthropic Claude
models, with some lemmas from Zhipu GLM and Moonshot Kimi models), directed and
audited by Joe Corneli. Most problems were closed by a per-problem solve loop.
The 95 that resisted it were closed by writing a blueprint for each problem and
proving its leaves in parallel, one agent per leaf. [`methods/`](methods/README.md) describes
that process in enough detail to repeat it:

- [`methods/01-statements.md`](methods/01-statements.md): how a problem
  statement is encoded, graded and registered;
- [`methods/02-blueprints.md`](methods/02-blueprints.md): how a blueprint is
  written and checked before any proof work starts;
- [`methods/03-lemma-seats.md`](methods/03-lemma-seats.md): how leaves are
  dispatched to agent "seats", checked, spliced back and landed;
- [`methods/04-library.md`](methods/04-library.md): how results too large
  for one seat become library work in `ConstructionTargets/`.

The full git history is public, including failed attempts and repairs.

## Repository layout

| path | contents |
|---|---|
| `problems/P/` | one bundle per problem: `problem.md`, `problem.tex`, `informal-solution.md`, `lean/Main.lean`, `status.json` |
| `problems/STATEMENTS.json` | the statement registry (fingerprints, grades, graders, evidence) |
| `apm/` | the problem sources in LaTeX |
| `ConstructionTargets/` | shared Lean library built for the problems (with `*.blueprint.md` sketches for library families) |
| `holes/labs/blueprints/P/` | per-problem blueprints |
| `holes/labs/lemmas/P/` | per-leaf seat files from the parallel rounds |
| `holes/labs/statement-registry/` | grading evidence and audits |
| `holes/labs/out-of-competition/` | narrower or partial results kept for reference; they do not count as closures |
| `scripts/` | registry, status and checking tools |
| `docs/` | technical notes written during the campaign |
| `methods/` | how the work was done (start here if you want to reproduce it) |

Problem ids read as subject, year, session, number: `t00J02` is topology,
2000, January exam, problem 2 (`A` is the August exam; `apm/manifest.edn`
records the two sessions as fall and spring). The subject letters are
`a` (real and complex analysis), `b` (algebra), `m` (applied mathematics) and
`t` (topology).

## License

The problem statements are copyright The University of Texas at Austin
(the exam year is in each file and in `apm/manifest.edn`) and are used with
permission. Everything else in this repository is released under
[CC0 1.0](https://creativecommons.org/publicdomain/zero/1.0/). See
[`LICENSE`](LICENSE).

## Acknowledgements

The prelim problems are used with the permission of the University of Texas
at Austin, which in 2002 told Joe Corneli he could use them as he saw fit.
We are grateful for that permission, which made this project possible.

Mathlib, Lean and their communities supplied almost every tool the proofs rely
on.
