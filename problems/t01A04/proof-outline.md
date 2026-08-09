# Proof Outline: t01A04

The canonical Lean attempt is `lean/Main.lean`. The two concrete sheet points
are normalized, while the quotient-cover and fundamental-group computations
remain open.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01A04.md`

## Compiled progress

- `apm_t01a04_sheetPoint_zero` and `apm_t01a04_sheetPoint_one` identify the
  two gluing points used in both total spaces.
- `apm_t01a04_sheetPoint_sq` proves both gluing points square to `1`, the
  compatibility needed by the quotient projections.
- `apm_t01a04_circleCoverMap` and `apm_t01a04_torusCoverMap` are the actual
  continuous maps from the two concrete quotient total spaces to the wedge.
  Their representative maps respect `Relation.EqvGen`, and both basepoint
  equations are proved.
- `apm_t01a04_circleCoverMap_surjective` and
  `apm_t01a04_torusCoverMap_surjective` prove both quotient maps are onto,
  using the packaged surjectivity of circle squaring on the doubled pieces.

## Remaining boundary

- Prove a Seifert--van Kampen theorem for the concrete quotient wedge and
  obtain the presentation `ℤ² * ℤ`.
- Certify the two now-constructed quotient maps as covering maps by an
  evenly-covered-neighborhood gluing argument.
- Identify their induced fundamental-group ranges with the parity kernels.
- Compute enough singular homology of the quotient total spaces to rule out a
  homeomorphism (`H₂ ≅ ℤ²` versus `H₂ ≅ ℤ`).

## Hop 4 bridge statements

- `apm_t01A04_bridge_quotient_maps_are_coverings` states the missing local
  evenly-covered-neighborhood theorem for both descended quotient maps.
- `apm_t01A04_bridge_piOne_presentation_and_ranges` states the complete
  `ℤ² * ℤ` universal presentation, its two parity characters, and the
  equality of their kernels with the two inclusion-induced ranges.
- `apm_t01A04_bridge_total_spaces_not_homeomorphic` states the consequence of
  the singular `H₂` computation: the two concrete total spaces are not
  homeomorphic.

Choosing the concrete maps in the frozen existential, the first bridge gives
the covering clauses, the second supplies all group-theoretic data and range
clauses, and the third supplies the final distinction.
