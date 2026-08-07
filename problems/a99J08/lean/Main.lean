import Mathlib

/-!
# APM a99J08: A square-root bound at a mixed-boundary corner

## Statement repairs

1. The source writes `D = {z : |z| < 1}` followed by `Im(z) = y > 0`.
   This is interpreted as the open upper half-disk, as required for the two
   stated conditions to be boundary conditions.
2. The quotient `|g(z)| / |z|^(1/2)` is undefined at `z = 0`, although the
   source asks for boundedness on all of `closure D`. We state the equivalent
   global estimate `|g(z)| ≤ C * sqrt |z|`, which is meaningful at the corner.

## Encoding questions

None.
-/

open Set Complex

noncomputable section

/-- The open upper half of the complex unit disk. -/
def apm_a99J08_upperHalfDisk : Set ℂ :=
  Metric.ball 0 1 ∩ {z | 0 < z.im}

/-- Squaring converts a purely imaginary boundary value into a real one. -/
lemma apm_a99J08_sq_im_eq_zero_of_re_eq_zero (z : ℂ) (hz : z.re = 0) :
    (z ^ 2).im = 0 := by
  simp [pow_two, Complex.mul_im, hz]

/-- Squaring preserves reality of a boundary value. -/
lemma apm_a99J08_sq_im_eq_zero_of_im_eq_zero (z : ℂ) (hz : z.im = 0) :
    (z ^ 2).im = 0 := by
  simp [pow_two, Complex.mul_im, hz]

/-- The mixed boundary conditions become one real-boundary condition after
squaring, away from the corner. -/
lemma apm_a99J08_sq_real_on_punctured_diameter
    (g : ℂ → ℂ)
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0)
    {x : ℝ} (hx₁ : -1 < x) (hx₂ : x < 1) (hx₀ : x ≠ 0) :
    ((g x) ^ 2).im = 0 := by
  rcases lt_or_gt_of_ne hx₀ with hx | hx
  · exact apm_a99J08_sq_im_eq_zero_of_im_eq_zero _ (hneg x hx₁ hx)
  · exact apm_a99J08_sq_im_eq_zero_of_re_eq_zero _ (hpos x hx hx₂)

theorem apm_a99j08
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk)
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closure apm_a99J08_upperHalfDisk,
        ‖g z‖ ≤ C * Real.sqrt ‖z‖ := by
  /-
  PARTIAL boundary (closer hop 1): the key algebraic reduction is now compiled
  above. `apm_a99J08_sq_real_on_punctured_diameter` proves that `g²` has zero
  imaginary part on the punctured diameter, turning the two mixed boundary
  conditions into the single boundary condition needed for Schwarz reflection.

  I inspected `ConstructionTargets.HerglotzRigidity`: its
  `conj_apply_conj_eq` proves the symmetry of an already entire function, but
  does not construct a holomorphic extension from one half-disk. Mathlib's
  removable-singularity API likewise starts only after such an extension is
  available. The remaining bridge is therefore a local Schwarz-reflection
  construction for `g²` across `(-1,1)`, including continuity at zero; after
  that, factor the reflected function by `z`, bound the quotient on a smaller
  closed disk, and combine this with compactness away from zero.
  -/
  sorry
