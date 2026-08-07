# Proof Outline: b01A01

The frozen theorem is fully proved in `lean/Main.lean`.

For each `a`, split on whether `a = b^p`:

- If so, `sub_pow_char` rewrites `X^p - C (b^p)` as `(X - C b)^p`,
  which splits by `Splits.X_sub_C` and `Splits.pow`.
- Otherwise, Mathlib's `X_pow_sub_C_irreducible_of_prime` proves the
  polynomial irreducible directly.

For the second conjunct, the assumed surjectivity is definitionally the
surjectivity of `frobenius k p`. `PerfectRing.ofSurjective` constructs a
perfect ring, `PerfectRing.toPerfectField` constructs a perfect field, and
`PerfectField.separable_of_irreducible` is exactly the desired conclusion.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b01A01.md`

## Verification

- `lake env lean problems/b01A01/lean/Main.lean` exits successfully.
- The main theorem contains no `sorry`.
