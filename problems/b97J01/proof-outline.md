# Proof Outline: b97J01

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
Three of the five conjuncts are now packaged as complete helper lemmas.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97J01.md`

## Compiled progress

- `S₅` is not solvable, translated to the custom derived-series definition.
- Every nontrivial finite prime-power group has nontrivial center.
- Every finite prime-power group is nilpotent, translated to the custom lower
  central-series definition.

## Remaining bridge

Prove concretely that `S₃` has terminating derived series but nonterminating
lower central series. This requires explicit commutator/series calculations or
a structural self-normalizing-subgroup argument.
