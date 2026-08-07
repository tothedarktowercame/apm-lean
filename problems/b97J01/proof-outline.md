# Proof Outline: b97J01

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
Four of the five conjuncts are now packaged as complete helper lemmas.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97J01.md`

## Compiled progress

- `S₅` is not solvable, translated to the custom derived-series definition.
- Every nontrivial finite prime-power group has nontrivial center.
- Every finite prime-power group is nilpotent, translated to the custom lower
  central-series definition.
- `S₃` is not nilpotent: its explicit transposition subgroup is proper and
  self-normalizing, contradicting the normalizer condition for nilpotent groups.

## Remaining bridge

Prove that `S₃` has terminating derived series. The remaining route is to use
the abelian normal subgroup `A₃` and the sign quotient, or explicitly show the
second derived subgroup is trivial.
