# Proof Outline: a03J08

## Problem

Let F be a finite subset of ℂ, D = ℂ \ F. Let f be analytic on D with
|f(z)| → ∞ as |z| → ∞ and as z → z_α for each z_α ∈ F. Show f(D) = ℂ.

## Formalisation Approach

### Proof strategy

By contradiction: suppose w₀ ∉ f(D). Define g(z) = 1/(f(z) - w₀).
- g is analytic on D (since f ≠ w₀ on D)
- ‖g‖ → 0 near each point of F (since ‖f‖ → ∞ there)
- ‖g‖ → 0 at infinity
- By Riemann removable singularity, g extends to entire function g_ext
- By Liouville (eq_const_of_tendsto_cocompact), g_ext ≡ 0
- But g ≠ 0 on D. Contradiction.

### Proven infrastructure (zero-sorry)

1. `tendsto_norm_sub_atTop`: ‖f‖ → ∞ implies ‖f - w₀‖ → ∞ (reverse triangle)
2. `tendsto_norm_reciprocal_zero`: ‖f‖ → ∞ implies ‖(f-w₀)⁻¹‖ → 0
3. `hg_diff`: g = (f-w₀)⁻¹ differentiable on Fᶜ (DifferentiableOn.inv)
4. `hg_poles`: ‖g‖ → 0 near each z_α ∈ F
5. `hg_infty`: ‖g‖ → 0 at cocompact
6. `hg_ext_infty`: g_ext → 0 at cocompact (g_ext = g on Fᶜ, F compact)
7. Liouville: g_ext ≡ 0 via `Differentiable.eq_const_of_tendsto_cocompact`
8. Contradiction: g_ext ≠ 0 on D (since (f-w₀)⁻¹ ≠ 0)

### Remaining sorry (1 sorry)

`hg_entire`: g_ext is `Differentiable ℂ`. Requires extending g across the
finite set F using the Riemann removable singularity theorem
(`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`).
At z ∈ F: g_ext is differentiable on a punctured neighborhood (from hg_diff)
and continuous at z (from hg_poles). At z ∉ F: g_ext equals (f-w₀)⁻¹ near z
since F is closed/finite. The sorry is at the interface between the
if-then-else definition, the finite set structure, and Mathlib's analytic API.

### Key Mathlib tools

- `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
  (Riemann removable singularity)
- `Differentiable.eq_const_of_tendsto_cocompact` (Liouville)

## Lean state

- **Checked:** exit 0, 0 errors, 1 sorry
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a03J08/lean/Main.lean`

## References

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a03J08.md`
