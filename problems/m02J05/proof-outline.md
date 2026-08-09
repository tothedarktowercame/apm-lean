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

## Hop 4 bridge statements

- `apm_m02J05_bridge_convex_and_submodule` states convexity of the modular
  class and realizes the rescalable class as a real submodule of `AEEqFun`.
- `apm_m02J05_bridge_luxemburg_laws` states the full `sInf` gauge theory:
  nonnegativity, definiteness, absolute homogeneity, and the triangle
  inequality.
- `apm_m02J05_bridge_complementary_young_holder` states pointwise Young's
  inequality for the inverse pair and the resulting integral estimate with
  constant two.

The three bridge conclusions concatenate verbatim into the frozen theorem's
remaining conjunction.
