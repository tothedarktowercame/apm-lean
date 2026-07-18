import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.DSlope

/-!
# APM a92J04: A self-map of the disk tangent to the identity must be the identity

**Problem.** Let Δ = {z ∈ ℂ : |z| < 1}. Suppose Σ_{n=2}^∞ aₙzⁿ converges
absolutely for all z ∈ Δ, and |z + Σ_{n=2}^∞ aₙzⁿ| < 1 for all z ∈ Δ.
Prove that aₙ = 0 for all n ≥ 2.

## Proof strategy

By the Schwarz lemma equality case: f(z) = z + Σ aₙzⁿ maps Δ to Δ with
f(0) = 0 and f'(0) = 1, so ‖f'(0)‖ = 1. By the rigidity case of the
Schwarz lemma (Mathlib's `affine_of_mapsTo_ball_of_norm_dslope_eq_div`),
f must be affine: f(z) = f(0) + dslope f 0 0 • z = deriv f 0 • z = z.
So f = id, hence all coefficients aₙ vanish.

## Statement repair note

The informal proof proposes encoding the problem via a coefficient sequence
and a `tsum`. The key structural repair: Mathlib's Schwarz lemma uses
`MapsTo f (ball c R₁) (closedBall (f c) R₂)` — it maps to a **closed** ball.
Since the problem gives `|f(z)| < 1` (open ball), and open ball ⊆ closed ball,
this is a strengthening, so the Mathlib lemma applies directly.
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Set Metric
open scoped Topology

namespace ApmCanaries.A92J04

/-! ## Schwarz lemma equality case for disk self-maps -/

/-- If f : ball 0 1 → ball 0 1 is analytic with f(0) = 0 and deriv f 0 = 1,
    then f(z) = z for all z in the disk.

    This is the equality case of the Schwarz lemma. -/
theorem disk_selfmap_deriv_one_eq_identity
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hf_maps : ∀ z ∈ ball (0 : ℂ) 1, f z ∈ ball (0 : ℂ) 1)
    (hf_zero : f 0 = 0)
    (hf_deriv : deriv f 0 = 1) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = z := by
  -- The open-ball map implies a closed-ball map
  have h_maps_closed : MapsTo f (ball (0 : ℂ) 1) (closedBall (f 0) 1) := by
    intro z hz
    rw [hf_zero, mem_closedBall]
    exact le_of_lt (mem_ball.mp (hf_maps z hz))
  -- Apply the equality case: ‖dslope f 0 0‖ = ‖deriv f 0‖ = ‖1‖ = 1 = 1/1
  have h_dslope : dslope f 0 0 = deriv f 0 := dslope_same f 0
  have h_eq : ‖dslope f 0 0‖ = 1 / 1 := by
    rw [h_dslope, hf_deriv, one_div, inv_one, norm_one]
  have h_00 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_self]; norm_num
  -- Equality case: f z = f 0 + (z - 0) • dslope f 0 0
  have hθ : EqOn f (fun z => f 0 + (z - 0) • dslope f 0 0) (ball (0 : ℂ) 1) :=
    affine_of_mapsTo_ball_of_norm_dslope_eq_div hf_holo h_maps_closed h_00 h_eq
  -- Simplify: f 0 = 0, dslope f 0 0 = deriv f 0 = 1, so f z = z
  intro z hz
  have := hθ hz
  simp only [sub_zero, h_dslope, hf_deriv, smul_eq_mul, mul_one, hf_zero, zero_add] at this
  exact this

/-! ## Main theorem -/

/-- Main theorem: if f(z) = z + Σ_{n≥2} aₙzⁿ maps Δ into Δ,
    then f(z) = z for all z ∈ Δ.

    **SORRY BOUNDARY:** Connecting the power series representation
    `f(z) = z + Σ a(n+2) z^(n+2)` to `DifferentiableOn ℂ` requires showing the
    power series defines an analytic function on the disk. Mathlib's
    `HasFPowerSeriesOnBall` / `AnalyticAt` infrastructure can do this, but
    connecting `Summable (fun n => a n * z^n)` to `DifferentiableOn` requires
    building the analytic structure from the summability hypothesis.
    Once DifferentiableOn is established, the result follows directly from
    `disk_selfmap_deriv_one_eq_identity` above. -/
theorem disk_selfmap_tangent_identity
    {a : ℕ → ℂ}
    (hconv : ∀ z ∈ ball (0 : ℂ) 1, Summable (fun n => a (n + 2) * z ^ (n + 2)))
    (hf_maps : ∀ z ∈ ball (0 : ℂ) 1,
      ‖z + ∑' n, a (n + 2) * z ^ (n + 2)‖ < 1) :
    ∀ n, 2 ≤ n → a n = 0 := by
  sorry

/-- Direct version: if f : ℂ → ℂ is differentiable on the disk, maps disk to disk,
    fixes 0, and has deriv f 0 = 1, then f = id. -/
theorem disk_selfmap_tangent_identity' (f : ℂ → ℂ)
    (hf_holo : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hf_maps : ∀ z ∈ ball (0 : ℂ) 1, f z ∈ ball (0 : ℂ) 1)
    (hf_zero : f 0 = 0)
    (hf_deriv : deriv f 0 = 1) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = z :=
  disk_selfmap_deriv_one_eq_identity hf_holo hf_maps hf_zero hf_deriv

end ApmCanaries.A92J04
