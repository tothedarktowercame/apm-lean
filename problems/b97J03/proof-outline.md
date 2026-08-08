# Proof Outline: b97J03

The frozen theorem has a compiling partial formalization in `lean/Main.lean`.
For the special polynomial, the two evident roots are formally shown distinct
and contained in every embedded root field.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97J03.md`

## Compiled progress

- Every root satisfies `α⁶ = 2` and is nonzero.
- `-α` is also a root, and both `α` and `-α` lie in `ℚ(α)`.
- Consequently the special root count is at least two for every complex root.
- Every restricted root count for a nonzero polynomial is at most its degree.
- The special polynomial has degree six, so its count lies between two and six.
- `apm_b97j03_special_factorization` explicitly factors the mapped polynomial
  into the six linear factors `X - ζ^i α`, using a fixed primitive sixth root
  of unity in `ℂ`.

## Remaining bridge

Use the compiled six-factor formula to exclude the four factors with
`i ≠ 0,3` from `ℚ(α)`, obtaining the exact count two.
For the general theorem, formalize the transitive Galois action and identify
the restricted root count with a normalizer/stabilizer index, yielding
divisibility and the abelian equality case.
