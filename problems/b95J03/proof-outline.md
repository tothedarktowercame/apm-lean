# Proof Outline: b95J03

The theorem is fully proved in `lean/Main.lean` with no sorries.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b95J03.md`

## Completed formal steps

- The universal-property characterization, image dimension, and generic kernel
  dimension are complete.
- The two displayed complex tensors are proved to lie in the kernel.
- Their linear independence is now proved without a tensor basis: the tensor
  functionals `re ⊗ re` and `re ⊗ im` extract their two coefficients.
- Given the kernel finrank equality, Mathlib's
  `basisOfLinearIndependentOfCardEqFinrank` constructs the requested basis and
  the two displayed values are verified.

## Closed dimension bridge

- `tensorMulRepresentation_finrank_ker` packages the generic rank-nullity
  computation.
- `tensorMulRepresentation_finrank_ker_of_finrank_eq` accepts an explicit
  numerical finrank equality in the same typeclass context. Specializing it
  with the locally established `Module.finrank ℝ ℂ = 2` avoids the module
  instance diamond and proves that the kernel has finrank two.
- The two independent displayed vectors therefore form a basis via
  `basisOfLinearIndependentOfCardEqFinrank`.

## Audit

- `lake env lean problems/b95J03/lean/Main.lean`: exit 0.
- The main theorem has no `sorryAx` dependency.
