# Proof Outline: a92J03

## Problem

For f ∈ L¹(ℝ), define f̂(ξ) = ∫ f(x) e^{ixξ} dx. Prove:
(a) f̂ is continuous,
(b) ‖f̂‖_∞ ≤ ‖f‖₁,
(c) Deduce: f ↦ f̂ maps L¹(ℝ) into C₀(ℝ).

## Formalisation Approach

### Statement repair

The problem uses the convention `e^{ixξ}` (no 2π factor). Mathlib's `𝓕`
uses `exp(-2πivw * I)`. We define our own `fourierTransform` following the
problem's convention and prove the three parts directly.

### Proven parts (zero-sorry)

1. **Part (b)** `fourierTransform_norm_le`: `‖f̂(ξ)‖ ≤ ∫ ‖f(x)‖ dx`
   via `norm_integral_le_integral_norm` + `|exp(ixξ)| = 1`.

2. **Part (a)** `fourierTransform_continuous`: f̂ is continuous
   via `continuous_of_dominated` (DCT): integrand `f(x)e^{ixξ}` is continuous
   in ξ, dominated by `‖f(x)‖` (since `|e^{ixξ}| = 1`).

3. **Full theorem** `fourier_maps_L1_to_C0`: combines (a), (b), (c).

### Remaining sorry (1 sorry)

**Part (c)** `fourierTransform_tendsto_zero`: Riemann-Lebesgue lemma.
Mathlib has `Real.tendsto_integral_exp_smul_cocompact` proving
`∫ 𝐞(-(v*w)) • f v → 0` at cocompact. The problem's convention `exp(ixξ)`
differs by the 2π factor. The conversion requires:
- Showing `exp(ixξ) = 𝐞(x*ξ/(2π))` (unfolding fourierChar, Circle.smul)
- Composing with the cocompact-preserving map `ξ ↦ -ξ/(2π)`

Both are routine but require Mathlib AddChar/Circle API navigation.

## Lean state

- **Checked:** exit 0, 0 errors, 1 sorry
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a92J03/lean/Main.lean`

## References

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a92J03.md`
- Key Mathlib: `continuous_of_dominated`, `norm_integral_le_integral_norm`,
  `Real.tendsto_integral_exp_smul_cocompact`
