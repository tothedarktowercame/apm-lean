# Proof Outline: b97J01

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
All five conjuncts are packaged as complete helper lemmas.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97J01.md`

## Compiled progress

- `S₅` is not solvable, translated to the custom derived-series definition.
- Every nontrivial finite prime-power group has nontrivial center.
- Every finite prime-power group is nilpotent, translated to the custom lower
  central-series definition.
- `S₃` is not nilpotent: its explicit transposition subgroup is proper and
  self-normalizing, contradicting the normalizer condition for nilpotent groups.
- `S₃` is solvable: `A₃` is verified commutative, it is the kernel of the sign
  map, and `solvable_of_ker_le_range` combines it with the commutative sign
  target.

## Closure

Closer hop 3 completed the sign-extension route and the main theorem now
assembles all helpers without any `sorry`.
