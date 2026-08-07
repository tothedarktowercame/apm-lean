# Proof Outline: m03J01

The frozen theorem has a partial Lean development with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m03J01.md`

## Compiled progress

- `apm_m03J01_riesz` constructs the continuous Fréchet--Riesz solution
  operator on an arbitrary real Hilbert space.
- `apm_m03J01_inner_riesz` proves its defining identity
  `inner ℝ (T f) v = f v`.
- `apm_m03J01_abstract_variational` proves the complete abstract first
  conjunct: boundedness below, attainment, uniqueness, and the Riesz identity.

## Remaining boundary

- quotient the custom value/gradient representatives by a.e. equality and
  establish their complete energy Hilbert structure;
- lift the forcing integral to the resulting dual space and descend the Riesz
  solution to `apm_m03J01_H01`;
- construct the weak-Hessian Banach space and formalize the closed-graph
  argument yielding the uniform `ENNReal` estimate.
