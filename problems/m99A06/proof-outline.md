# Proof Outline: m99A06

The canonical Lean attempt is `lean/Main.lean`. It establishes all raw-function
integrability prerequisites for the fixed-point construction.

- `m99A06_selfConvolution_integrable` uses the proved Young-convolution library.
- `m99A06_sin_mul_selfConvolution_integrable` applies the bounded sine
  multiplier.
- `m99A06_gaussian_integrable` proves forcing integrability.
- `m99A06_fixedPointMap_integrable` proves that the full nonlinear self-map
  sends every raw integrable representative to another integrable function.

## Remaining Boundary

- Transport convolution and the self-map to the complete `L¹` quotient.
- Establish Young's norm inequality and the quadratic Lipschitz estimate.
- Apply `ContractingWith.exists_fixedPoint'` on a complete closed ball.
- Select a raw representative and translate its fixed-point equality to the
  almost-everywhere `IsM99A06Solution` predicate.
