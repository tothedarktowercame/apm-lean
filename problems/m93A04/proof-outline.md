# Proof Outline: m93A04

The frozen Lean theorem is present in `lean/Main.lean`. The abstract
Neumann-series stage is now closed: any continuous endomorphism `T` with
`‖T‖ < 1` has bijective complement `1 - T`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93A04.md`

## Remaining boundary

- construct the parameterized continuous-kernel operator `Tₓ`;
- prove `‖Tₓ‖ ≤ c`, using the unit volume of the interval subtype;
- rewrite `D x = 1 - Tₓ` and invoke the proved bijectivity helper;
- package differentiation under the parameterized integral, including the
  uniform remainder, measurability, and domination hypotheses.

Mathlib's `isUnit_one_sub_of_norm_lt_one` handles inversion. Its dominated
parametric-integral lemmas are relevant to differentiability, but no searched
artifact supplies the required concrete continuous-map/operator packaging.
