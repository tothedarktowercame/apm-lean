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
- `apm_b97A01_conjugacy_exhaustive` checks that the five concrete classes
  exhaust `S₄`; `apm_b97A01_complete_conjugacy_classification` combines this
  with the structural equivalences, closing the complete first conjunct.

## Remaining bridge

Classify normal subgroups of `S₄`, prove solvability and the universal
order-24 action theorem, and
establish the structural Sylow and nonisomorphism facts for `SL₂(F₃)`.

## Hop 4 bridge statements

- `apm_b97A01_bridge_normal_subgroups` states the complete normal-subgroup
  lattice `1, V₄, A₄, S₄`.
- `apm_b97A01_bridge_S4_solvable` states solvability, obtainable from the
  corresponding normal series with abelian factors.
- `apm_b97A01_bridge_order24_action` states the universal theorem for an
  arbitrary finite group of order 24 with a nonnormal Sylow 3-subgroup.
- `apm_b97A01_bridge_SL23_structure` states the two remaining concrete facts:
  `SL₂(F₃)` is not isomorphic to `S₄` and has a nonnormal Sylow
  3-subgroup.

Together with the already proved cardinality of `SL₂(F₃)`, these four
contracts are exactly the remaining tail of the frozen conjunction.
