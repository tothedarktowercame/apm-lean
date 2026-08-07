# Proof Outline: b97A04

The canonical Lean attempt now compiles with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97A04.md`

## Compiled progress

- `apm_b97a04_module_finite` chooses a nonzero cyclic vector in the simple
  module and transfers finite generation from `R` to `V`.
- `apm_b97a04_schur_and_scalars` proves the three Schur-theoretic conjuncts:
  nonzero endomorphisms are units, the endomorphism space is finite over
  `ℂ`, and every `R`-endomorphism is scalar.

## Remaining bridge

Identify the Jacobson-density double centralizer with `Module.End ℂ V` and
bundle faithfulness and surjectivity as `R ≃ₐ[ℂ] Module.End ℂ V`. Then
transport semisimplicity and isotypy across this equivalence for arbitrary
`R`-modules and apply `IsIsotypicOfType.linearEquiv_finsupp`.
