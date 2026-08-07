# Proof Outline: b94J02

The Lean proof is complete in `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b94J02.md`

## Formal proof

- Nilpotence gives zero trace through Mathlib's
  `Matrix.isNilpotent_trace_of_isNilpotent`.
- The trace pairing is proved nondegenerate by choosing an elementary matrix
  that extracts each entry of `C`.
- An idempotent matrix is converted to an idempotent linear endomorphism;
  `LinearMap.IsProj.trace` identifies its trace with the dimension of its range,
  and the matrix rank API supplies the final equality.
