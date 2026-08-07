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

## Remaining bridge

Sharpen the general degree-six upper bound by excluding the other four sixth
roots from `ℚ(α)` to obtain the exact count two.
For the general theorem, formalize the transitive Galois action and identify
the restricted root count with a normalizer/stabilizer index, yielding
divisibility and the abelian equality case.
