# Proof Outline: b95J03

The Lean proof is partial in `lean/Main.lean`.

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

## Remaining bridge

Specialize the already-proved generic kernel dimension formula to `ℂ/ℝ` in a
way that avoids the competing `Module ℝ ℂ` instance parameters exposed by the
local rank-nullity calculation. Factoring the generic dimension conjunct into a
named helper before assembling the theorem should provide the cleanest route.
