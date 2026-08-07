# Proof Outline: b03J03

The Lean proof is complete in `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b03J03.md`

## Formal proof

- The universal UFD assertion is the standard Mathlib integrally-closed instance.
- `AdjoinRoot (X^2 - 5)` is identified explicitly with `Zsqrtd 5` by mutual
  evaluation maps. This supplies the domain and characteristic-zero structures.
- In its fraction field, `x = (1 + root) / 2` satisfies the monic equation
  `x^2 - x - 1 = 0`, so it is integral.
- If `x` came from the quadratic order, clearing the denominator and mapping to
  `Zsqrtd 5` would give `2 * y.re = 1`, an integer parity contradiction.
