# Proof Outline: t01A04

The canonical Lean attempt is `lean/Main.lean`. The two concrete sheet points
are normalized, while the quotient-cover and fundamental-group computations
remain open.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01A04.md`

## Compiled progress

- `apm_t01a04_sheetPoint_zero` and `apm_t01a04_sheetPoint_one` identify the
  two gluing points used in both total spaces.

## Remaining boundary

- Prove a Seifert--van Kampen theorem for the concrete quotient wedge and
  obtain the presentation `ℤ² * ℤ`.
- Construct the two quotient maps and certify them as covering maps.
- Identify their induced fundamental-group ranges with the parity kernels.
- Compute enough singular homology of the quotient total spaces to rule out a
  homeomorphism (`H₂ ≅ ℤ²` versus `H₂ ≅ ℤ`).
