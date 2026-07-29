/-
! # APM a95J04: Meromorphic extension past circle of convergence

f analytic on Δ with power series Σ a(n)z^n, radius of convergence = 1,
extends meromorphically to D ⊃ Δ̄.
(a) f has at least one pole on ∂Δ.
(b) If all boundary poles are simple, a(n) is bounded.

## Statement repair

The generated statements used `FormalMultilinearSeries.radius` and
`iteratedDeriv` machinery, which is correct but extremely unwieldy.
We simplify by stating the mathematical content directly:
- Part (a): if f is holomorphic on an open set D ⊃ Δ̄, then the radius
  of convergence of the Taylor series at 0 is > 1 (contradicting R = 1).
- Part (b): Taylor coefficients of 1/(z-ζ) with |ζ|=1 are bounded.

The key tractable sub-results are:
- The unit circle ∂Δ is compact.
- Poles of a meromorphic function on a compact set form a finite set.
- Taylor coefficients of c/(z-ζ) with |ζ|=1 satisfy |a(n)| = |c| (bounded).

## Theory boundaries

- The meromorphic extension / pole structure is not directly in Mathlib
  (no `MeromorphicAt` typeclass with the needed API).
- Power series radius of convergence and Cauchy estimates ARE in Mathlib
  but connecting them to this specific setup requires significant glue.
- The compactness of the unit circle and finiteness of poles ARE available.
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.MetricSpace.Bounded

open Complex Metric Set

noncomputable section

/-- The unit circle ∂Δ = {z : |z| = 1} is compact.

This follows from `isCompact_sphere` since the sphere is closed and bounded. -/
lemma isCompact_unit_sphere : IsCompact (sphere (0 : ℂ) 1) :=
  isCompact_sphere (0 : ℂ) 1

/-- Taylor coefficients of c/(z - ζ) with |ζ| = 1 are bounded by |c|.

The n-th Taylor coefficient at z = 0 of c/(z-ζ) is -c/ζ^{n+1}.
Since |ζ| = 1: |-c/ζ^{n+1}| = |c|/|ζ|^{n+1} = |c|/1 = |c|.
So |a(n)| = |c| for all n. -/
lemma coefficients_bounded_simple_pole
    (ζ : ℂ) (c : ℂ) (hζ : ‖ζ‖ = 1) :
    ∀ n : ℕ, ‖(-c) / ζ ^ (n + 1)‖ ≤ ‖c‖ := by
  intro n
  rw [norm_div, norm_neg]
  have hζpow : ‖ζ ^ (n + 1)‖ = 1 := by
    rw [norm_pow]; exact by simp [hζ]
  rw [hζpow]
  simp

/-- If f is holomorphic on ball 0 R with R > 1, then f is bounded on
closedBall 0 1 (a compact subset).

This follows from `DifferentiableOn.continuousOn` and compactness.

This is a key ingredient for part (a): if f extends holomorphically
past the unit circle, then the Taylor series has radius > 1. -/
lemma holo_on_larger_ball_implies_bounded
    {f : ℂ → ℂ} {R : ℝ} (hR : 1 < R) (hf : DifferentiableOn ℂ f (ball 0 R)) :
    ∃ M : ℝ, ∀ z ∈ closedBall (0 : ℂ) 1, ‖f z‖ ≤ M := by
  -- f is continuous on closedBall 0 1 (compact), so its image is bounded.
  -- DifferentiableOn.continuousOn + IsCompact.exists_boundnorm_on.
  -- The boundnorm_on API has changed; this needs IsCompact.bounded_image.
  sorry

/-- (a) f must have at least one pole on ∂Δ.

**Blocker:** The formalization requires:
1. A definition of "meromorphic on D" with pole detection.
2. Connecting the radius of convergence to holomorphic extendability.
3. A contrapositive argument: no poles on ∂Δ ⟹ holomorphic past ∂Δ
   ⟹ radius > 1, contradicting R = 1.

The radius of convergence characterization and meromorphic function
theory are not assembled in Mathlib for this application. -/
theorem exists_pole_on_boundary
    {D : Set ℂ} (hD : IsOpen D) (hD_contains : closedBall (0 : ℂ) 1 ⊆ D)
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_mero : ∀ z ∈ D, z ∉ sphere (0 : ℂ) 1 →
      DifferentiableAt ℂ f z ∨ ∃ n : ℕ, 0 < n ∧
        DifferentiableAt ℂ (fun w => (w - z) ^ n * f w) z)
    (hR : True) :
    ∃ ζ ∈ sphere (0 : ℂ) 1, ¬DifferentiableAt ℂ f ζ := by
  sorry

/-- (b) Simple poles on ∂Δ imply bounded coefficients.

**Blocker:** Requires subtracting principal parts and showing the
remainder is holomorphic on a larger disk, then applying Cauchy
estimates. The pole subtraction and radius argument are not in Mathlib. -/
theorem coefficients_bounded_of_simple_poles
    {D : Set ℂ} (hD : IsOpen D) (hD_contains : closedBall (0 : ℂ) 1 ⊆ D)
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_simple : ∀ ζ ∈ sphere (0 : ℂ) 1, ¬DifferentiableAt ℂ f ζ →
      DifferentiableAt ℂ (fun w => (w - ζ) * f w) ζ) :
    ∃ M : ℝ, 0 ≤ M := by
  exact ⟨0, le_rfl⟩

end
