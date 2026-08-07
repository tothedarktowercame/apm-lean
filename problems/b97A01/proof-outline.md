# Proof Outline: b97A01

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
The order of the concrete special linear group and the cycle types of all
chosen `S₄` class representatives are formally verified.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97A01.md`

## Compiled progress

- `apm_b97A01_SL23_card` proves `|SL₂(F₃)| = 24`.
- `apm_b97A01_representative_cycleTypes` computes the four nonidentity cycle
  types used in the conjugacy classification.

## Remaining bridge

Enumerate all `Fin 4` cycle types and conjugacy-class cardinalities, classify
normal subgroups of `S₄`, prove solvability and the universal order-24 action
theorem, and establish the structural Sylow and nonisomorphism facts for
`SL₂(F₃)`.
