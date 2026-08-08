# Proof Outline: m02J05

The frozen theorem has a partial Lean development with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02J05.md`

## Compiled progress

- the Young primitive vanishes at zero;
- the zero `AEEqFun` belongs to both `apm_m02J05_K α` and
  `apm_m02J05_L α`.
- the Young primitive is nonnegative on the nonnegative half-line;
- the Young primitive is monotone there, by interval-integral monotonicity.

## Remaining boundary

- upgrade the compiled nonnegativity and monotonicity of the Young primitive
  to convexity from strict monotonicity of `α`;
- build the submodule structure on the rescalable modular class;
- develop the `sInf` theory needed for positivity, definiteness, homogeneity,
  and the triangle inequality of the Luxemburg functional;
- formalize complementary Young's inequality for the inverse pair `α`, `β`,
  then derive the normalized integral estimate.
