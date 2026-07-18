# Proof Outline: a92J04

## Problem

Let Δ = {z ∈ ℂ : |z| < 1}. Suppose Σ_{n=2}^∞ aₙzⁿ converges absolutely
for all z ∈ Δ, and |z + Σ_{n=2}^∞ aₙzⁿ| < 1 for all z ∈ Δ.
Prove that aₙ = 0 for all n ≥ 2.

## Formalisation Approach

### Proof strategy

By the Schwarz lemma equality case: f(z) = z + Σ aₙzⁿ maps Δ to Δ with
f(0) = 0 and f'(0) = 1. Since ‖f'(0)‖ = 1 = R₂/R₁, the equality case of
the Schwarz lemma (Mathlib's `affine_of_mapsTo_ball_of_norm_dslope_eq_div`)
forces f to be affine: f(z) = f(0) + z • deriv f 0 = z. Hence f = id
and all coefficients vanish.

### Statement repair

The informal proof uses `MapsTo f (ball 0 1) (ball 0 1)` (open ball). Mathlib's
Schwarz lemma uses `MapsTo f (ball c R₁) (closedBall (f c) R₂)` (closed ball).
Since open ball ⊆ closed ball, the open-ball hypothesis implies the closed-ball
hypothesis needed by Mathlib.

### Proven zero-sorry

1. **`disk_selfmap_deriv_one_eq_identity`**: If f maps ball 0 1 to ball 0 1,
   f(0) = 0, and deriv f 0 = 1, then f(z) = z on the disk. Uses:
   - `affine_of_mapsTo_ball_of_norm_dslope_eq_div` (Schwarz equality case)
   - `dslope_same` (dslope at center = deriv)

2. **`disk_selfmap_tangent_identity'`**: Same result stated via DifferentiableOn.

### Remaining sorry (1 sorry)

**`disk_selfmap_tangent_identity`**: Connects the power series representation
`f(z) = z + Σ a(n+2)z^(n+2)` to `DifferentiableOn ℂ f (ball 0 1)`. Requires
showing the power series defines an analytic function on the disk from the
pointwise summability hypothesis. Once DifferentiableOn is established, the
result follows immediately from `disk_selfmap_deriv_one_eq_identity`.

## Lean state

- **Checked:** exit 0, 0 errors, 1 sorry
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a92J04/lean/Main.lean`

## References

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a92J04.md`
- Key Mathlib: `affine_of_mapsTo_ball_of_norm_dslope_eq_div` (Schwarz equality)
