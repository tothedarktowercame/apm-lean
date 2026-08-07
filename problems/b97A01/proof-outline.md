# Proof Outline: b97A01

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
The order of the concrete special linear group and the cycle types of all
chosen `S₄` class representatives are formally verified. Their conjugacy
characterizations and all five conjugacy-class cardinalities now compile.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97A01.md`

## Compiled progress

- `apm_b97A01_SL23_card` proves `|SL₂(F₃)| = 24`.
- `apm_b97A01_representative_cycleTypes` computes the four nonidentity cycle
  types used in the conjugacy classification.
- `apm_b97A01_conjugacy_classification` connects those computations to
  `Equiv.Perm.isConj_iff_cycleType_eq`.
- `apm_b97A01_conjugacy_class_cards` proves class sizes `1, 6, 3, 8, 6`
  using `Equiv.Perm.card_isConj_eq`.

## Remaining bridge

Prove the exhaustive `Fin 4` cycle-type disjunction, classify normal subgroups
of `S₄`, prove solvability and the universal order-24 action theorem, and
establish the structural Sylow and nonisomorphism facts for `SL₂(F₃)`.
